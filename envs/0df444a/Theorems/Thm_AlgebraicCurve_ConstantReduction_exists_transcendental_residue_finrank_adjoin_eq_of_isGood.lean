-- Prove2me | Theorems.Thm_AlgebraicCurve_ConstantReduction_exists_transcendental_residue_finrank_adjoin_eq_of_isGood
-- name    : AlgebraicCurve.ConstantReduction.exists_transcendental_residue_finrank_adjoin_eq_of_isGood
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/c5bedd20-a9de-51f3-bd05-2209f28b81e3
-- title:
--   Good constant reduction is defectless at some transcendental element
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring with residue field $k =$ `IsLocalRing.ResidueField A`, and $F$ a field equipped with an $L$-algebra structure such that for some $x \in F$ transcendental over $L$ the extension $F / L(x)$ is finite. Let $\bar F$ be a field equipped with a $k$-algebra structure, and let $R$ be a constant reduction of $F$ along $A$ onto $\bar F$: that is, a valuation subring $\mathcal{O} =$ `R.integers` of $F$ together with a surjective ring homomorphism `R.residue` from $\mathcal{O}$ onto $\bar F$ whose kernel is the maximal ideal of $\mathcal{O}$, and a map `R.placeMap` from places of $F/L$ to places of $\bar F/k$, subject to: $\mathrm{alg}_{L \to F}(c) \in \mathcal{O}$ if and only if $c \in A$; compatibility of `R.residue` with the residue map of $A$ on elements of $A$; every nonzero $f \in F$ has an $L$-multiple lying in $\mathcal{O}$ with nonzero residue; `R.placeMap` preserves the degree of a place; and, for $f \in \mathcal{O}$ with nonzero residue, the pushforward along `R.placeMap` of the principal divisor of $f$ computes the orders of `R.residue f` at the places of $\bar F/k$. Assume $R$ is good, i.e. `genusFF` $k\,\bar F =$ `genusFF` $L\,F$, where `genusFF` of a function field is the dimension, over the constant field, of $H^1$ of the zero divisor. Then there exists $x \in \mathcal{O}$ such that `R.residue x` is transcendental over $k$, the degree of $\bar F$ over $k(\mathrm{R.residue}\, x)$ is strictly positive, and $[F : L(x)] = [\bar F : k(\mathrm{R.residue}\, x)]$ as `Module.finrank`s.
--
--   This is Deuring's statement that a good constant reduction of a one-variable function field is a defectless prolongation of a Gauss valuation: in general only the inequality $[\bar F : k(\bar x)] \le [F : L(x)]$ is available for elements with transcendental residue, and goodness forces equality at a suitable $x$. It is used in the comparison of degree-zero divisor class groups under constant reduction and in lifting Riemann–Roch spaces from the reduction of a modular curve to the curve itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ConstantReduction_exists_transcendental_residue_finrank_adjoin_eq_of_isGood.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.ConstantReduction.exists_transcendental_residue_finrank_adjoin_eq_of_isGood
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (F : Type*) [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧ FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    (Fbar : Type*) [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) (hR : R.IsGood) :
    ∃ x : R.integers, Transcendental (IsLocalRing.ResidueField A) (R.residue x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar := by sorry
