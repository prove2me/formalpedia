-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_riemannGenusReachedAt_of_bounded
-- name    : AlgebraicCurve.exists_riemannGenusReachedAt_of_bounded
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/9408f96a-fdcd-5ff4-ae71-dcf44e54ec59
-- title:
--   The bound deg D-ℓ(D)≤γ-1 is attained
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume `IsCurveOver K F`: every nonzero $f \in F$ has a divisor, i.e. a finitely supported function $D$ on the places of $F/K$ (valuation subrings of $F$ containing the image of $K$, different from $F$, with principal ideals) whose value at each $v$ is $v.\mathrm{ord}\,f$ and whose degree is $0$; each place has residue field finite over $K$; and $\Omega_{F/K}$ is free of rank one over $F$. Assume further that the Riemann–Roch space of the zero divisor, $\{f \in F : v(f) \le 1 \text{ for all } v\}$, is finite-dimensional over $K$, and that $\deg D - \ell(D)$ is bounded above as $D$ ranges over all divisors, where the degree of $D$ is $\sum_v D(v)\deg v$ and `ell D` is the natural number playing the role of $\ell(D)$ for `LSpace D` $= \{f : v.\mathrm{adicValuation}\,f \le \exp(D v)$ for all $v\}$. Then the supremum is attained: there exist $\gamma \in \mathbb{Z}$ and a divisor $D_0$ such that `LSpace D₀` is finite-dimensional over $K$, $\deg D_0 - \ell(D_0) = \gamma - 1$, and $\deg D - \ell(D) \le \gamma - 1$ for every divisor $D$.
--
--   This is the step in the construction of the genus of a one-variable function field which passes from boundedness of $\deg D - \ell(D)$ to attainment of the maximum, the integer $\gamma$ then being the genus; it rests on the fact that a nonempty set of integers bounded above has a greatest element. It is used in the existence of a place avoiding a given divisor with all orders equal to one, and in the proof that the Serre pairing and its transpose are bijective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_riemannGenusReachedAt_of_bounded.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem exists_riemannGenusReachedAt_of_bounded {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    (hbdd : RiemannGenusBounded K F) :
    ∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀ := by sorry
