-- Prove2me | Theorems.Thm_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension
-- name    : AlgebraicCurve.card_places_deg_one_eq_sum_divisors_of_constantFieldExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/5f1187dc-d1d9-5770-a5e8-7b806f354b8d
-- title:
--   Rational places in a constant field extension
-- statement:
--   Let $k$ and $k'$ be finite fields, $F$ and $F'$ fields, with $k$-algebra structures on $k'$, $F$ and $F'$, a $k'$-algebra structure on $F'$ and an $F$-algebra structure on $F'$, all compatible (the towers $k \subseteq k' \subseteq F'$ and $k \subseteq F \subseteq F'$ commute with the given maps), and assume $F'$ is integral over $F$. Assume $F$ is a curve over $k$ and $F'$ a curve over $k'$ in the sense of the predicate [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): for a curve over $K$ one requires that every nonzero $f$ admits a divisor $D$ with $D(v) = \operatorname{ord}_v(f)$ at every place $v$ and $\deg D = 0$, that every residue field of a place is finite-dimensional over $K$, and that the module of Kähler differentials $\Omega_{F/K}$ is free of rank one over $F$; here a place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, different from $F$, whose underlying ring is a principal ideal ring, and its degree is the $K$-dimension of its residue field. Assume further that $F$ is essentially of finite type over $k$, that $F'$ is generated as an $F$-algebra by the image of $k'$, and that every element of $F$ algebraic over $k$ already lies in the image of $k$. Then the number of places of $F'$ over $k'$ of degree $1$ equals $\sum_{d \mid [k':k]} d \cdot \#\{v \text{ a place of } F \text{ over } k : \deg v = d\}$, the sum being over the positive divisors of $[k':k] = \operatorname{finrank}_k k'$ and the cardinalities being `Nat.card`.
--
--   This is the splitting law for places in a constant field extension of a global function field: the rational places of $F' = F\cdot k'$ are precisely those above the places of $F$ whose degree divides $[k':k]$, each such place of degree $d$ carrying exactly $d$ of them. It is used in the construction of a divisor of degree one on a curve over a finite field and in the estimate [`AlgebraicCurve.sum_divisors_mul_card_places_lt_of_even`](thm.html#AlgebraicCurve.sum_divisors_mul_card_places_lt_of_even).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.card_places_deg_one_eq_sum_divisors_of_constantFieldExtension
    {k k' F F' : Type*} [Field k] [Finite k] [Field k'] [Finite k'] [Field F] [Field F']
    [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
    [Algebra k F] [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    [AlgebraicCurve.IsCurveOver k F] [Algebra.EssFiniteType k F]
    [AlgebraicCurve.IsCurveOver k' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap k' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic k y → y ∈ (algebraMap k F).range) :
    Nat.card {w : AlgebraicCurve.Place k' F' | w.deg = 1} =
      ∑ d ∈ Nat.divisors (Module.finrank k k'),
        d * Nat.card {v : AlgebraicCurve.Place k F | v.deg = d} := by sorry
