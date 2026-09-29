-- Prove2me | Theorems.Thm_AlgebraicCurve_ComponentChart_ord_residue_pos_iff_of_isCentre_of_comap_eq
-- name    : AlgebraicCurve.ComponentChart.ord_residue_pos_iff_of_isCentre_of_comap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/0e589c49-292e-5675-873d-1d98d8103149
-- title:
--   Positivity of ord_Q of a reduction is σ-invariant
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ an extension field of $L$, and $\bar F$ an extension field of the residue field of $A$. Let $\sigma$ be an $L$-algebra automorphism of $F$, let $C$ be a `ComponentChart` for $A$, $F$, $\bar F$ (a valuation subring $C.integers \subseteq F$ with surjective reduction map $C.residue$ onto $\bar F$ whose kernel is the maximal ideal, a set $C.dom$ of places of $F/L$, a finite set of nodes, and a map $C.placeMap$ to places of $\bar F$ over the residue field of $A$, subject to the compatibility axioms of that structure), and let $N$ be a finite set of places of $\bar F$ over the residue field of $A$. Assume that the chart obtained by transport along $\sigma$ has the same integers as $C$, i.e. the preimage of $C.integers$ under $\sigma$ is $C.integers$, and the same domain, i.e. $\{P : \sigma \cdot P \in C.dom\} = C.dom$, and that every place in $C.dom$ is rational, meaning the structure map from $L$ to its residue field is surjective. Let $O \subseteq F$ be a valuation subring whose preimage under $\sigma$ is $O$, and let $Q$ be a place of $\bar F$ which is a centre of $(C, N)$ for $O$: $Q \notin N$, and for every $f \in C.integers$ satisfying $C.tubeBounded$ (that is, $f$ lies in the valuation subring of each $P \in C.dom$ and $P.evalAt\,f \in A$), the reduction $C.residue\,f$ either vanishes or has $\mathrm{ord}_Q > 0$ exactly when $f$ lies in $O$ and in its maximal ideal. Then for every $f \in F$ with $f \in C.integers$, $\sigma f \in C.integers$ and $f$ tube-bounded, one has $\mathrm{ord}_Q(C.residue\,f) > 0$ if and only if $\mathrm{ord}_Q(C.residue\,\sigma f) > 0$, where $\mathrm{ord}_Q$ is minus the logarithm of the $Q$-adic valuation.
--
--   This is the equivariance of the centre of a valuation ring under an automorphism preserving the chart: the condition that the reduction of a tube-bounded chart-integral element be positive at the centre $Q$ is insensitive to replacing $f$ by $\sigma f$. It is used in the analysis of charts on modular curves of full level, in the three lemmas identifying the integers of a component chart fixed by a level automorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ComponentChart_ord_residue_pos_iff_of_isCentre_of_comap_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_AlgebraicCurve_AffinoidCentre

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AlgebraicCurve

open IsLocalRing
open scoped Pointwise

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem ComponentChart.ord_residue_pos_iff_of_isCentre_of_comap_eq (σ : F ≃ₐ[L] F) (C : ComponentChart A F Fbar)
    (N : Finset (Place (ResidueField A) Fbar))
    (hint : (C.comap σ).integers = C.integers) (hdom : (C.comap σ).dom = C.dom)
    (hrat : ∀ P ∈ C.dom, P.IsRational)
    (O : ValuationSubring F) (hfix : O.comap σ.toAlgHom.toRingHom = O)
    {Q : Place (ResidueField A) Fbar} (hQ : C.IsCentre N O Q)
    (f : F) (hf : f ∈ C.integers) (hσf : σ f ∈ C.integers) (hbd : C.tubeBounded f) :
    0 < Q.ord (C.residue ⟨f, hf⟩) ↔ 0 < Q.ord (C.residue ⟨σ f, hσf⟩) := by sorry
