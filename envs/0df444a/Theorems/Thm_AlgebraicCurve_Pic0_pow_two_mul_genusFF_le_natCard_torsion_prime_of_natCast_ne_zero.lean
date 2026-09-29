-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_pow_two_mul_genusFF_le_natCard_torsion_prime_of_natCast_ne_zero
-- name    : AlgebraicCurve.Pic0.pow_two_mul_genusFF_le_natCard_torsion_prime_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/e8df4061-0fe7-5379-81de-2ad1efac1d1e
-- title:
--   Lower bound ℓ^{2g} for ℓ-torsion of Pic⁰
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra and $K$ algebraically closed, and assume $F$ is a one-variable function field over $K$ in the sense that there is an $x \in F$ transcendental over $K$ with $F$ finite-dimensional over the intermediate field $K(x)$. Assume further `IsCurveOver K F`: every nonzero $f \in F$ admits a finitely supported divisor whose coefficient at each place $v$ is $v.\mathrm{ord}(f)$ and whose degree is $0$, the residue field of each place is a finite $K$-module, and the module of Kähler differentials $\Omega[F/K]$ is free of rank one over $F$; here a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring. Let $\ell$ be a prime whose image in $K$ is nonzero. Then $\ell^{2\,\mathrm{genusFF}(K,F)} \le \#\,\mathrm{Pic}^0(K,F)[\ell]$, where $\mathrm{Pic}^0(K,F)$ is the group of degree-zero divisors modulo principal divisors, $[\ell]$ denotes the $\mathbb{Z}$-torsion submodule killed by $\ell$, $\mathrm{genusFF}(K,F)$ is the $K$-dimension of the first adelic cohomology $H^1(0)$ of the zero divisor, and the cardinality is the natural-number cardinality (so the inequality also asserts finiteness of the $\ell$-torsion).
--
--   This is the lower-bound half of the classical count $\#\,\mathrm{Pic}^0(F/K)[\ell] = \ell^{2g}$ for a curve of genus $g$ over an algebraically closed constant field, for primes $\ell$ invertible in $K$, stated here purely in function-field terms. It feeds the comparison of $\ell$-torsion under a constant reduction, being cited in the proof that every $\ell$-torsion class on the special fibre lifts to an $\ell$-torsion class with prescribed reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_pow_two_mul_genusFF_le_natCard_torsion_prime_of_natCast_ne_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.pow_two_mul_genusFF_le_natCard_torsion_prime_of_natCast_ne_zero
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) :
    ℓ ^ (2 * genusFF K F) ≤ Nat.card (Pic0.torsion K F ℓ) := by sorry
