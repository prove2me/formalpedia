-- Prove2me | Theorems.Thm_AlgebraicCurve_ComponentChart_exists_algEquiv_residue_eq_and_placeMap_eq_smul_of_integers_eq_of_dom_eq_of_hasDiscFibres
-- name    : AlgebraicCurve.ComponentChart.exists_algEquiv_residue_eq_and_placeMap_eq_smul_of_integers_eq_of_dom_eq_of_hasDiscFibres
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/d989e281-603d-57fa-b2c9-52cbfa634f54
-- title:
--   Rigidity of disc-fibred component charts
-- statement:
--   Fix a prime $q$, a natural number $M'\neq 0$, a valuation subring $A$ of $\overline{\mathbb Q}$ with residue field $\kappa=\mathrm{ResidueField}\,A$, and write $F=$ `fieldBar q M'` for the full-level modular function field over $\overline{\mathbb Q}$. Let $\bar F$ be a field, equipped with a $\kappa$-algebra structure, which is a curve over $\kappa$ in the sense of `IsCurveOver` (principal divisors of degree zero exist for every nonzero element, every place has residue field finite over $\kappa$, and $\Omega_{\bar F/\kappa}$ is free of rank one over $\bar F$) and is essentially of finite type over $\kappa$. Let $C,C'$ be component charts of $F$ along $A$ with values in $\bar F$: each consists of a valuation subring `integers` of $F$ contracting to $A$, a surjective residue homomorphism `residue` onto $\bar F$ whose kernel is the maximal ideal and which is compatible with reduction on $A$, a set `dom` of places of $F$ over $\overline{\mathbb Q}$, a finite set `nodes` of places of $\bar F$ over $\kappa$, and a map `placeMap` from places of $F$ to places of $\bar F$, subject to the axioms of `ComponentChart` (scaling into the integers with nonzero residue, places of `dom` reducing outside `nodes`, compatibility of evaluation with reduction at rational places of `dom`, and the order formula for push-forward divisors at non-nodes). Assume $C'.\mathrm{integers}=C.\mathrm{integers}$ and $C'.\mathrm{dom}=C.\mathrm{dom}$, and that both charts have disc fibres: for every place $Q$ of $\bar F$ over $\kappa$ outside the chart's nodes there is an element $T$ of the chart's integers whose residue is nonzero and has order $1$ at $Q$, such that every $P$ in `dom` with $\mathrm{placeMap}\,P=Q$ has $T$ in its valuation ring with $P.\mathrm{evalAt}\,T$ in the maximal ideal of $A$, and such that for every $c$ in the maximal ideal of $A$ there is exactly one $P\in\mathrm{dom}$ with $\mathrm{placeMap}\,P=Q$ and $P.\mathrm{evalAt}\,T=c$. The conclusion is the existence of a $\kappa$-algebra automorphism $\theta$ of $\bar F$ such that: for every $f\in F$ lying in both charts' integers, $C'.\mathrm{residue}(f)=\theta\bigl(C.\mathrm{residue}(f)\bigr)$; for every place $Q$ of $\bar F$ over $\kappa$, the translate of $Q$ by the semilinear automorphism $(\theta,\mathrm{id}_\kappa)$ lies in $C'.\mathrm{nodes}$ if and only if $Q\in C.\mathrm{nodes}$; and for every $P\in C.\mathrm{dom}$, $C'.\mathrm{placeMap}\,P$ is the translate of $C.\mathrm{placeMap}\,P$ by that same semilinear automorphism.
--
--   This is a rigidity statement for the formal fibres of a chart of a semistable covering: the valuation ring of the generic point of a component together with its domain of places determines the residue map, the nodes and the reduction of places, up to the single $\kappa$-automorphism of the reduced curve by which the two residue maps differ. It is applied to transport the reduction of places along a field automorphism of $F$ preserving a chart's valuation ring and domain, and is used in the vanishing criteria for cuspidal specialisations at full level, [`ModularCurve.FullLevel.eq_zero_of_cuspidalSpecialization_eq_zero_of_forall_sum_unipotent_eq_zero_of_semistableCovering_of_reduction`](thm.html#ModularCurve.FullLevel.eq_zero_of_cuspidalSpecialization_eq_zero_of_forall_sum_unipotent_eq_zero_of_semistableCovering_of_reduction) and its variants for $q=2$ and $q=3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ComponentChart_exists_algEquiv_residue_eq_and_placeMap_eq_smul_of_integers_eq_of_dom_eq_of_hasDiscFibres.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel AlgebraicCurve IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem AlgebraicCurve.ComponentChart.exists_algEquiv_residue_eq_and_placeMap_eq_smul_of_integers_eq_of_dom_eq_of_hasDiscFibres
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [IsCurveOver (ResidueField A) Fbar] [Algebra.EssFiniteType (ResidueField A) Fbar]
    (C C' : ComponentChart A (fieldBar q M') Fbar)
    (hO : C'.integers = C.integers) (hdom : C'.dom = C.dom)
    (hC : SemistableCovering.HasDiscFibres C) (hC' : SemistableCovering.HasDiscFibres C') :
    ∃ θ : Fbar ≃ₐ[ResidueField A] Fbar,
      (∀ (f : fieldBar q M') (h : f ∈ C.integers) (h' : f ∈ C'.integers), C'.residue ⟨f, h'⟩ = θ (C.residue ⟨f, h⟩)) ∧
      (∀ Q : Place (ResidueField A) Fbar, SemilinearAut.ofAlgAut θ • Q ∈ C'.nodes ↔ Q ∈ C.nodes) ∧
      ∀ P ∈ C.dom, C'.placeMap P = SemilinearAut.ofAlgAut θ • C.placeMap P := by sorry
