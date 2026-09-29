-- Prove2me | Theorems.Thm_AlgebraicCurve_RiemannGenusReachedAt_eq_of_ge
-- name    : AlgebraicCurve.RiemannGenusReachedAt.eq_of_ge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/451ade33-aa6b-51ea-b041-40c1c8a99770
-- title:
--   deg D-ℓ(D) is constant above a genus-realising divisor
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra satisfying `IsCurveOver K F`: every nonzero $f \in F$ has a divisor, i.e. a finitely supported integer-valued function on the places $v$ of $F/K$ whose value at each $v$ is $v.\mathrm{ord}(f)$ and whose degree is $0$; each place has residue field finite over $K$; and the module of Kähler differentials $\Omega[F/K]$ is free of rank one over $F$. Assume moreover that $F/K$ has at least one place and that $\mathrm{LSpace}(0)$, the $K$-subspace $\{f \in F : v(f) \le 1 \text{ for all } v\}$, is finite-dimensional over $K$. Here a divisor is a finitely supported function $D$ from places to $\mathbb{Z}$, its degree is $\sum_v D(v)\,\deg v$ with $\deg v$ the degree of the residue field at $v$ over $K$, $\mathrm{LSpace}(D) = \{f \in F : v(f) \le \exp(D(v)) \text{ for all } v\}$, and $\ell(D)$ is its $K$-dimension. Let $\gamma \in \mathbb{Z}$ and let $D_0$ be a divisor satisfying `RiemannGenusReachedAt γ D₀`, that is: $\mathrm{LSpace}(D_0)$ is finite-dimensional over $K$, $\deg D_0 - \ell(D_0) = \gamma - 1$, and $\deg D - \ell(D) \le \gamma - 1$ for every divisor $D$. Then for every divisor $D$ with $D_0 \le D$ (pointwise), $\deg D - \ell(D) = \gamma - 1$.
--
--   This is the stabilisation step in the classical development of the Riemann inequality: once the supremum $\gamma - 1$ of $\deg D - \ell(D)$ is attained at some divisor $D_0$, it is attained at every larger divisor, since the quantity is monotone increasing in $D$ and bounded above. It is used in the project's treatment of the adelic index, the Riemann–Roch and Čech–Riemann–Roch statements, the count of effective divisors, and the surjectivity of residue maps for regular prolongations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RiemannGenusReachedAt_eq_of_ge.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem RiemannGenusReachedAt.eq_of_ge {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {D : Divisor K F} (hD : D₀ ≤ D) :
    Divisor.degree D - ell D = γ - 1 := by sorry
