-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
-- name    : AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/b195282b-b847-503a-90fb-7f28d01c87d8
-- title:
--   Uniqueness of a regular prolongation from its trace on L(x)
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field extension of $L$, and $\bar F$ a field extension of the residue field $k = \mathrm{ResidueField}(A)$. Let $R$ be a regular prolongation of $A$ to $F$ with values in $\bar F$, that is: a valuation subring $\mathcal O = R.\text{integers}$ of $F$, a ring homomorphism $\mathrm{res} \colon \mathcal O \to \bar F$ such that an element of $L$ lies in $A$ exactly when its image in $F$ lies in $\mathcal O$, $\mathrm{res}$ is surjective with kernel the maximal ideal of $\mathcal O$, $\mathrm{res}$ agrees on $A$ with the composite of the residue map $A \to k$ and $k \to \bar F$, and every nonzero $f \in F$ admits $c \in L$ with $c \cdot f \in \mathcal O$ and $\mathrm{res}(c \cdot f) \neq 0$. Let $x \in \mathcal O$ be such that $\bar x = \mathrm{res}(x)$ is transcendental over $k$, suppose $\bar F$ has positive (hence finite) dimension over the intermediate field $k(\bar x) \subseteq \bar F$, and suppose $[F : L(x)] = [\bar F : k(\bar x)]$. Then for any valuation subring $V$ of $F$ such that, for every $e$ in the intermediate field $L(x) \subseteq F$, one has $e \in V$ if and only if $e \in \mathcal O$, it follows that $V = \mathcal O$.
--
--   This is the uniqueness half of Deuring's description of the regular prolongations of a valuation ring to a function field: under the stated degree equality, a regular prolongation is determined by its intersection with the rational subfield $L(x)$. It serves to discharge hypotheses in the construction and comparison of places of $F$ over $A$, and is used in the results on existence and uniqueness of prolongations with prescribed residue data and on reduction of the $x$-model of a curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (V : ValuationSubring F)
    (hV : ∀ e : F, e ∈ IntermediateField.adjoin L {(x : F)} → (e ∈ V ↔ e ∈ R.integers)) :
    V = R.integers := by sorry
