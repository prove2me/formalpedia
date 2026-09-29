-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_natCard_torsion_pow_eq_pow_two_mul_genusFF_mul_of_charZero
-- name    : AlgebraicCurve.Pic0.natCard_torsion_pow_eq_pow_two_mul_genusFF_mul_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/3c23ab1f-6cbf-5516-b8d8-a0e99b58bc90
-- title:
--   ℓ^k-torsion of Pic⁰ has order ℓ^{2gk} in characteristic zero
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ algebraically closed of characteristic zero, $F$ essentially of finite type over $K$, and assume `IsCurveOver K F`: every nonzero $f \in F$ admits a finitely supported divisor $D$ on the set of places of $F/K$ (valuation subrings of $F$ that contain the image of $K$, are proper, and are principal ideal rings) with $D(v) = \mathrm{ord}_v(f)$ for all $v$ and $\deg D = 0$; every place has residue field finite over $K$; and the module of Kähler differentials $\Omega_{F/K}$ is free of rank $1$ over $F$. Write $\mathrm{Pic}^0(K,F)$ for the quotient of the group of degree-zero divisors by the subgroup of divisors of nonzero elements of $F$, and $g = \mathrm{genusFF}(K,F)$ for the $K$-dimension of $H^1$ of the zero divisor. Then for every prime $\ell$ and every $k \in \mathbb{N}$, the subgroup of elements of $\mathrm{Pic}^0(K,F)$ killed by $\ell^k$ (the $\mathbb{Z}$-torsion submodule for the scalar $\ell^k$) satisfies $\#\,\mathrm{Pic}^0(K,F)[\ell^k] = \ell^{2gk}$. Since the right-hand side is nonzero and cardinality is taken in the `Nat.card` sense, this includes the assertion that this torsion subgroup is finite.
--
--   This is the classical count of the $\ell^k$-torsion of the Jacobian of a curve of genus $g$ over an algebraically closed field of characteristic zero, $J[n] \cong (\mathbb{Z}/n)^{2g}$, phrased for the degree-zero divisor class group of a one-variable function field. It feeds the torsion estimates used for Picard groups of nodal curves and for the computation of component groups and specialisation maps on semistable models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_natCard_torsion_pow_eq_pow_two_mul_genusFF_mul_of_charZero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.natCard_torsion_pow_eq_pow_two_mul_genusFF_mul_of_charZero
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) :
    Nat.card (Pic0.torsion K F (ℓ ^ k)) = ℓ ^ (2 * genusFF K F * k) := by sorry
