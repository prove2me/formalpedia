-- Prove2me | Theorems.Thm_AlgebraicCurve_card_sub_one_mul_card_effectiveDivisors_eq
-- name    : AlgebraicCurve.card_sub_one_mul_card_effectiveDivisors_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/bf29eec7-5659-5551-9a90-05a85672901a
-- title:
--   Counting effective divisors of large degree over a finite field
-- statement:
--   Let $k$ be a finite field and $F$ a field extension of $k$ that is essentially of finite type over $k$ and satisfies [`AlgebraicCurve.IsCurveOver k F`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ admits a divisor whose coefficient at each place is $\mathrm{ord}_v(f)$ and whose degree is $0$, each place has residue field finite over $k$, and $\Omega_{F/k}$ is free of rank one over $F$. Here a place is a valuation subring of $F$, distinct from $F$, containing the image of $k$ and a principal ideal ring; a divisor is a finitely supported $\mathbb{Z}$-valued function on places, its degree being the sum of its coefficients weighted by the residue degrees; $\mathrm{Pic}^0(k,F)$ is the group of degree-zero divisors modulo the principal ones. Assume also `ConstantsAreBase k F`, i.e. the Riemann–Roch space $\mathcal{L}(0)$ is exactly the image of $k$ in $F$. Write $g = \mathrm{genusFF}(k,F) = \dim_k H^1(0)$. The assertion is that there exists $N \in \mathbb{N}$ with $g \le N$ such that for every $n \ge N$ for which some divisor of degree $n$ exists, $(\#k - 1)$ times the number of divisors $D \ge 0$ (pointwise) with $\deg D = n$ equals $\#\mathrm{Pic}^0(k,F) \cdot (\#k^{\,n+1-g} - 1)$, all cardinalities and subtractions being taken in $\mathbb{N}$. The threshold $N$ is only asserted to exist and to be at least $g$; no explicit value such as $2g-1$ is given.
--
--   This is the classical count of effective divisors of a fixed large degree on a curve over a finite field, in the form $(q-1)A_n = h\,(q^{\,n+1-g}-1)$, which follows from Riemann–Roch together with the fact that the effective divisors in a class $C$ correspond to $(\mathcal{L}(C) \setminus \{0\})/k^\times$. It is used in the evaluation of the $L$-polynomial of the function field at $1$ as the class number, in [`AlgebraicCurve.LPolynomial_eval_one_eq_natCard_pic0`](thm.html#AlgebraicCurve.LPolynomial_eval_one_eq_natCard_pic0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_card_sub_one_mul_card_effectiveDivisors_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.card_sub_one_mul_card_effectiveDivisors_eq
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [AlgebraicCurve.IsCurveOver k F] [Algebra.EssFiniteType k F]
    (hC : AlgebraicCurve.ConstantsAreBase k F) :
    ∃ N : ℕ, AlgebraicCurve.genusFF k F ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (∃ D : AlgebraicCurve.Divisor k F, AlgebraicCurve.Divisor.degree D = (n : ℤ)) →
        (Nat.card k - 1) * Nat.card {D : AlgebraicCurve.Divisor k F //
            0 ≤ D ∧ AlgebraicCurve.Divisor.degree D = (n : ℤ)} =
          Nat.card (AlgebraicCurve.Pic0 k F) *
            (Nat.card k ^ (n + 1 - AlgebraicCurve.genusFF k F) - 1) := by sorry
