-- Prove2me | Theorems.Thm_AlgebraicCurve_ell_add_of_forall_eq_ord
-- name    : AlgebraicCurve.ell_add_of_forall_eq_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/d1544b65-de20-54cf-8361-4cd5de25adac
-- title:
--   Adding a principal divisor does not change ℓ(D)
-- statement:
--   Let $K$ be a field and $F$ a field equipped with a $K$-algebra structure. A place of $F/K$ is a valuation subring of $F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring; a divisor is a finitely supported function from places to $\mathbb{Z}$, and for a place $v$ the integer $\mathrm{ord}_v(g)$ is minus the logarithm of the value of $g$ under the adic valuation attached to $v$. For a divisor $D$ write $\ell(D)$ for the $K$-dimension `Module.finrank K` of the Riemann–Roch space `riemannRochSpace D`, viewed as a $K$-submodule of $F$ (so $\ell(D)=0$ whenever that space is not finite-dimensional over $K$). The theorem asserts: given divisors $D$ and $P$ and an element $f \in F$ with $f \neq 0$ such that $P(v) = \mathrm{ord}_v(f)$ for every place $v$ of $F/K$ — that is, $P$ is the principal divisor of $f$, stated in unfolded form — one has $\ell(D + P) = \ell(D)$, where $D+P$ is the pointwise sum of the two finitely supported functions. No finiteness or separability hypothesis on $F/K$ enters.
--
--   This is the standard invariance of the dimension of a Riemann–Roch space under translation of the divisor by a principal divisor, the statement which makes $\ell$ a function on the divisor class group. It is used in the construction of the divisor class map for a curve model ([`AlgebraicCurve.CurveModel.exists_divisorClassMap`](thm.html#AlgebraicCurve.CurveModel.exists_divisorClassMap)) and in the analysis of divisors at which the Riemann genus bound is attained ([`AlgebraicCurve.exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt`](thm.html#AlgebraicCurve.exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ell_add_of_forall_eq_ord.lean

import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.ell_add_of_forall_eq_ord
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] (D : Divisor K F) {P : Divisor K F}
    {f : F} (hf : f ≠ 0) (hP : ∀ v : Place K F, P v = v.ord f) :
    ell (D + P) = ell D := by sorry
