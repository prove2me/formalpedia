-- Prove2me | Theorems.Thm_AlgebraicCurve_ComponentChart_comap_fibreParam_laws
-- name    : AlgebraicCurve.ComponentChart.comap_fibreParam_laws
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/723f12c4-22fe-56dd-8b91-8e1e1e1b4546
-- title:
--   Transport of a fibre parameter along a field automorphism
-- statement:
--   Let $L$ be a field, $A$ a valuation subring of $L$, $F$ a field over $L$ and $\bar F$ a field over the residue field of $A$; let $\sigma$ be an $L$-algebra automorphism of $F$, and let $C$ be a component chart for $A$, $F$, $\bar F$, i.e. a valuation subring $C.\mathrm{integers}$ of $F$ with a surjective ring homomorphism $C.\mathrm{residue}$ onto $\bar F$ whose kernel is the maximal ideal, a set $C.\mathrm{dom}$ of places of $F/L$ (valuation subrings of $F$ containing $L$, proper, with principal ideals), a finite set of nodes among places of $\bar F$ over the residue field of $A$, and a reduction map $C.\mathrm{placeMap}$ on places, subject to the chart axioms. Let $P$ be a place of $F/L$ which is rational, i.e. $L$ surjects onto its residue field, and let $T \in F$. Assume, writing $t := T - \iota\big((\sigma \cdot P).\mathrm{evalAt}\,T\big)$ with $\iota = \mathrm{algebraMap}\,L\,F$ and $\mathrm{evalAt}$ the evaluation of an element of a place's valuation ring in $L$ via the inverse of $L \to$ residue field, that $t \in C.\mathrm{integers}$ and: $C.\mathrm{residue}(t) \neq 0$; the order of $C.\mathrm{residue}(t)$ at the place $C.\mathrm{placeMap}(\sigma \cdot P)$ equals $1$; $\mathrm{ord}_{\sigma \cdot P}(t) > 0$; and $\mathrm{ord}_Q(t) = 0$ for every $Q \in C.\mathrm{dom}$ with $C.\mathrm{placeMap}\,Q = C.\mathrm{placeMap}(\sigma \cdot P)$ and $Q \neq \sigma \cdot P$. The conclusion is the same four conditions for the transported chart $C.\mathrm{comap}\,\sigma$ (integers the preimage of $C.\mathrm{integers}$ under $\sigma$, residue $f \mapsto C.\mathrm{residue}(\sigma f)$, domain $\{Q : \sigma \cdot Q \in C.\mathrm{dom}\}$, same nodes, reduction $Q \mapsto C.\mathrm{placeMap}(\sigma \cdot Q)$) at the place $P$ and the element $\sigma^{-1}T - \iota\big(P.\mathrm{evalAt}(\sigma^{-1}T)\big)$. No hypothesis that $\sigma \cdot P$ lie in $C.\mathrm{dom}$ is imposed.
--
--   The four conditions say that $t$ is a fibre parameter (local coordinate on the formal fibre) for the chart at the given place: it reduces to a uniformiser at the reduction of that place, vanishes there and is a unit at the other places of the chart domain with the same reduction. The statement is the transport of this property along an $L$-automorphism of $F$, and is used in the construction of semistable coverings of modular curves, where the charts on one component of the special fibre are obtained from those on another by pulling back along an automorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ComponentChart_comap_fibreParam_laws.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableChartsComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing AlgebraicCurve

theorem AlgebraicCurve.ComponentChart.comap_fibreParam_laws
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (σ : F ≃ₐ[L] F) (C : ComponentChart A F Fbar) (P : Place L F) (hPrat : P.IsRational) (T : F)
    (hT : ∃ h : T - algebraMap L F ((σ • P).evalAt T) ∈ C.integers,
      C.residue ⟨_, h⟩ ≠ 0 ∧ (C.placeMap (σ • P)).ord (C.residue ⟨_, h⟩) = 1 ∧
      0 < (σ • P).ord (T - algebraMap L F ((σ • P).evalAt T)) ∧
      ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap (σ • P) → Q ≠ σ • P →
        Q.ord (T - algebraMap L F ((σ • P).evalAt T)) = 0) :
    ∃ h : σ.symm T - algebraMap L F (P.evalAt (σ.symm T)) ∈ (C.comap σ).integers,
      (C.comap σ).residue ⟨_, h⟩ ≠ 0 ∧ ((C.comap σ).placeMap P).ord ((C.comap σ).residue ⟨_, h⟩) = 1 ∧
      0 < P.ord (σ.symm T - algebraMap L F (P.evalAt (σ.symm T))) ∧
      ∀ Q ∈ (C.comap σ).dom, (C.comap σ).placeMap Q = (C.comap σ).placeMap P → Q ≠ P →
        Q.ord (σ.symm T - algebraMap L F (P.evalAt (σ.symm T))) = 0 := by sorry
