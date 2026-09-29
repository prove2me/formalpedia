-- Prove2me | Theorems.Thm_AlgebraicCurve_ConstantReduction_exists_residue_mem_evalAt_mem_algebraMap_residue_eq_of_forall_ord_neg_placeMap_ne
-- name    : AlgebraicCurve.ConstantReduction.exists_residue_mem_evalAt_mem_algebraMap_residue_eq_of_forall_ord_neg_placeMap_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/fc6223f8-c431-5fc3-9f91-b950e3c29d2e
-- title:
--   Pointwise compatibility of a constant reduction at a rational place
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$ in which every nonzero element has a finitely supported divisor of degree zero recording its orders at all places (the hypothesis `HasPrincipalDivisors L F`); let $\bar F$ be a field that is an algebra over the residue field of $A$. Let $R$ be a constant reduction of $F$ along $A$ onto $\bar F$, that is: a valuation subring $R.\mathrm{integers} \subseteq F$, a ring homomorphism $R.\mathrm{residue}$ from it to $\bar F$, and a map $R.\mathrm{placeMap}$ from places of $F$ over $L$ to places of $\bar F$ over the residue field of $A$, subject to: $\mathrm{algebraMap}_{L\to F}(x)$ lies in $R.\mathrm{integers}$ exactly when $x \in A$; $R.\mathrm{residue}$ is surjective with kernel the maximal ideal of $R.\mathrm{integers}$ and compatible with the residue map of $A$ on elements of $A$; every nonzero $f \in F$ has a scalar multiple $c \cdot f$ in $R.\mathrm{integers}$ with nonzero residue; $R.\mathrm{placeMap}$ preserves the degree of a place; and, for $f \in R.\mathrm{integers}$ with $R.\mathrm{residue}\,f \neq 0$, the pushforward along $R.\mathrm{placeMap}$ of the divisor of $f$ is the divisor of $R.\mathrm{residue}\,f$. Here a place of $F$ over $L$ is a proper valuation subring of $F$ containing the image of $L$ whose ideals are principal, and $v.\mathrm{ord}$ is the associated normalised order function. Let $P$ be a place of $F$ over $L$ which is rational, i.e. $L$ maps onto the residue field of $P$, let $f \in F$ lie in $R.\mathrm{integers}$ and in the valuation subring of $P$, and assume that every place $P'$ with $P'.\mathrm{ord}\,f < 0$ satisfies $R.\mathrm{placeMap}\,P' \neq R.\mathrm{placeMap}\,P$. Then the reduction $R.\mathrm{residue}\,f$ lies in the valuation subring of the place $R.\mathrm{placeMap}\,P$, the value $P.\mathrm{evalAt}\,f \in L$ (the chosen $L$-preimage of the residue class of $f$ at $P$) lies in $A$, and the image of the residue class of $P.\mathrm{evalAt}\,f$ under the induced map from the residue field of $A$ to the residue field of $R.\mathrm{placeMap}\,P$ equals the residue class of $R.\mathrm{residue}\,f$ at $R.\mathrm{placeMap}\,P$.
--
--   This is the pointwise, or evaluation, compatibility of a constant reduction in the sense of Deuring: the value of a function at a rational place reduces to the value of the reduced function at the reduced place, under the proviso that no pole of the function specialises to that reduced place. It is used in the treatment of the modular curve of full level, in the lemmas producing rational integral functions with prescribed values and the lemmas constructing supersingular tubes from residues of evaluations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ConstantReduction_exists_residue_mem_evalAt_mem_algebraMap_residue_eq_of_forall_ord_neg_placeMap_ne.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ConstantReduction.exists_residue_mem_evalAt_mem_algebraMap_residue_eq_of_forall_ord_neg_placeMap_ne
    {L : Type} [Field L] {A : ValuationSubring L}
    {F : Type} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : ConstantReduction A F Fbar)
    (P : Place L F) (hP : P.IsRational)
    (f : F) (hf : f ∈ R.integers) (hfP : f ∈ P.toValuationSubring)
    (hpole : ∀ P' : Place L F, P'.ord f < 0 → R.placeMap P' ≠ R.placeMap P) :
    ∃ (hm : R.residue ⟨f, hf⟩ ∈ (R.placeMap P).toValuationSubring) (h : P.evalAt f ∈ A),
      algebraMap (ResidueField ↥A) (R.placeMap P).ResidueField (IsLocalRing.residue ↥A ⟨P.evalAt f, h⟩) =
        IsLocalRing.residue ↥(R.placeMap P).toValuationSubring ⟨R.residue ⟨f, hf⟩, hm⟩ := by sorry
