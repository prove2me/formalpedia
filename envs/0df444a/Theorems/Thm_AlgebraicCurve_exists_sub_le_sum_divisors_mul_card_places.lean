-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places
-- name    : AlgebraicCurve.exists_sub_le_sum_divisors_mul_card_places
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/f5925bc9-ccb5-5286-8b42-3ed5b8e28eba
-- title:
--   Bombieri's lower bound for Nᵣ along multiples of some m
-- statement:
--   Let $k$ be a finite field and $F$ a field extension of $k$ which is a curve over $k$ in the sense of the project: every nonzero $f \in F$ admits a divisor $D$ with $D(v) = \mathrm{ord}_v(f)$ at every place $v$ and $\deg D = 0$, every place of $F/k$ has residue field finite-dimensional over $k$, and $\Omega_{F/k}$ is free of rank one over $F$; here a place is a valuation subring of $F$ containing the image of $k$, different from $F$ itself and a principal ideal ring, and its degree is $\dim_k$ of its residue field. Assume further that $F$ is of essentially finite type over $k$ and that the constants are the base field, in the sense that the Riemann–Roch space $L(0)$ of the zero divisor equals the image of $k$ in $F$. Then there are an integer $m > 0$ and a real constant $c$ such that for every $r > 0$ divisible by $m$,
--   $$q^{r} + 1 - c\,\sqrt{q}^{\,r} \le \sum_{d \mid r} d \cdot \#\{v : \deg v = d\},$$
--   where $q = \#k$ and the right-hand side is the natural number $N_r$ viewed as a real number. No positivity is asserted for $c$.
--
--   This is the lower half of Bombieri's elementary proof of the Riemann hypothesis for curves over finite fields: the quantity $N_r = \sum_{d \mid r} d B_d$ counts the rational places of the constant field extension of degree $r$, and the bound is obtained only along multiples of a suitable $m$, which suffices for the asymptotic conclusion. It feeds into the determination of the absolute values of the roots of the zeta function, used by [`AlgebraicCurve.norm_eq_sqrt_of_mem_roots_of_natCard_fixedPoints_restrictAlong_eq`](thm.html#AlgebraicCurve.norm_eq_sqrt_of_mem_roots_of_natCard_fixedPoints_restrictAlong_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.exists_sub_le_sum_divisors_mul_card_places
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [AlgebraicCurve.IsCurveOver k F] [Algebra.EssFiniteType k F]
    (hC : AlgebraicCurve.ConstantsAreBase k F) :
    ∃ m : ℕ, 0 < m ∧ ∃ c : ℝ, ∀ r : ℕ, 0 < r → m ∣ r →
      (Nat.card k : ℝ) ^ r + 1 - c * Real.sqrt (Nat.card k : ℝ) ^ r ≤
        ((∑ d ∈ Nat.divisors r,
            d * Nat.card {v : AlgebraicCurve.Place k F | v.deg = d} : ℕ) : ℝ) := by sorry
