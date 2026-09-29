-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_natCard_torsion_prime_eq_pow_two_mul_genusFF_of_natCast_ne_zero
-- name    : AlgebraicCurve.Pic0.natCard_torsion_prime_eq_pow_two_mul_genusFF_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/b820b105-2f7e-598f-aabf-a4a90cfca141
-- title:
--   Order ℓ^{2g} for the ℓ-torsion of Pic⁰
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure, subject to two hypotheses. First, $F$ is a one-variable function field over $K$: there is an $x \in F$ transcendental over $K$ such that $F$ is finite-dimensional over the intermediate field $K(x)$. Second, `IsCurveOver K F` holds, i.e. every nonzero $f \in F$ admits a finitely supported divisor whose coefficient at each place $v$ is $v.\mathrm{ord}(f)$ and whose degree is $0$, every place has residue field finite over $K$, and the module of Kähler differentials $\Omega_{F/K}$ is free of rank $1$ over $F$; here a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$, and a principal ideal ring. Let $\ell$ be a prime with $\ell \neq 0$ in $K$. Then the subgroup of elements $z$ of $\mathrm{Pic}^0(F/K)$ — degree-zero divisors modulo principal divisors — with $\ell z = 0$ has exactly $\ell^{2g}$ elements, where $g = \operatorname{genusFF} K F$ is the $K$-dimension of $H^1$ of the zero divisor. Since the cardinality is the natural-number one, the equality includes the assertion of finiteness.
--
--   This is the function-field form of the classical count of $\ell$-division points on the Jacobian of a curve over an algebraically closed field: multiplication by $\ell$ is a separable isogeny of degree $\ell^{2g}$ when $\ell$ is invertible in the base. It is the level-one case from which the count at all powers $\ell^n$ is deduced, and it is cited by [`AlgebraicCurve.Pic0.natCard_torsion_pow_eq_pow_two_mul_genusFF_mul_of_charZero`](thm.html#AlgebraicCurve.Pic0.natCard_torsion_pow_eq_pow_two_mul_genusFF_mul_of_charZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_natCard_torsion_prime_eq_pow_two_mul_genusFF_of_natCast_ne_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.natCard_torsion_prime_eq_pow_two_mul_genusFF_of_natCast_ne_zero
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) :
    Nat.card (Pic0.torsion K F ℓ) = ℓ ^ (2 * genusFF K F) := by sorry
