-- Prove2me | Theorems.Thm_AlgebraicCurve_sum_divisors_mul_card_places_lt_of_even
-- name    : AlgebraicCurve.sum_divisors_mul_card_places_lt_of_even
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/25c2958e-e758-58d0-948e-8d174dca6d8d
-- title:
--   Bombieri's bound on places of a function field
-- statement:
--   Let $k$ be a finite field and $F$ a field equipped with a $k$-algebra structure such that $F$ is a curve over $k$ in the sense of the project's `IsCurveOver` class — every nonzero $f \in F$ has a divisor $D$ with $D(v) = \operatorname{ord}_v(f)$ at every place and $\deg D = 0$, every place has residue field finite over $k$, and $\Omega_{F/k}$ is free of rank one over $F$ — and such that $F$ is of essentially finite type over $k$; here a place $v$ is a valuation subring of $F$ containing the image of $k$, distinct from $F$ itself and a principal ideal ring, with $\deg v = \dim_k \kappa(v)$. Assume $k$ is the full constant field, in the form that the Riemann–Roch space $L(0)$ equals the image of $k$ in $F$. Write $g = \operatorname{genusFF} k F = \dim_k H^1(0)$ and $q = \#k$. Then for every even $r \in \mathbb{N}$ with $(g+1)^4 < q^r$ one has, as an inequality of real numbers,
--   $$\sum_{d \mid r} d \cdot \#\{v : \deg v = d\} < q^r + 1 + (2g+1)\,\sqrt{q}^{\,r},$$
--   the sum being over the positive divisors $d$ of $r$ and the cardinalities being `Nat.card` of the sets of places of degree $d$.
--
--   This is Bombieri's form of the upper bound in the Hasse–Weil estimate, obtained by Stepanov's elementary method: the left-hand side counts the places of degree one of the constant field extension $F\mathbb{F}_{q^r}$, whose genus is again $g$, and the bound is the Bombieri inequality $N < q' + 1 + (2g+1)\sqrt{q'}$ for a square $q' = q^r$ large compared with $g$. It feeds the Riemann hypothesis for curves over finite fields through the estimate on the absolute values of the roots of the zeta function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_sum_divisors_mul_card_places_lt_of_even.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.sum_divisors_mul_card_places_lt_of_even
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [AlgebraicCurve.IsCurveOver k F] [Algebra.EssFiniteType k F]
    (hC : AlgebraicCurve.ConstantsAreBase k F) (r : ℕ) (hr : Even r)
    (hq : (AlgebraicCurve.genusFF k F + 1) ^ 4 < Nat.card k ^ r) :
    ((∑ d ∈ Nat.divisors r,
        d * Nat.card {v : AlgebraicCurve.Place k F | v.deg = d} : ℕ) : ℝ) <
      (Nat.card k : ℝ) ^ r + 1 +
        (2 * (AlgebraicCurve.genusFF k F : ℝ) + 1) * Real.sqrt (Nat.card k : ℝ) ^ r := by sorry
