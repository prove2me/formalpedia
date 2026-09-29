-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/d86992d2-91cd-5e4b-a7cd-51c680a2c6b9
-- title:
--   Degree-r divisors over an algebraically closed field are sums of r points
-- statement:
--   Let $f\colon\mathcal C\to S$ be a separated morphism of schemes which is smooth of relative dimension $1$, let $k$ be an algebraically closed field and let $x\colon\operatorname{Spec}k\to S$ be a morphism; fix $r\in\mathbb N$. Let $D$ be a relative effective Cartier divisor of degree $r$ for $f$ along $x$, that is, a datum consisting of an ideal sheaf $D.I$ on the fibre product $\mathcal C\times_S\operatorname{Spec}k$ such that the closed immersion of the associated closed subscheme followed by the second projection to $\operatorname{Spec}k$ is finite, flat and locally of finite presentation, and has fibre rank exactly $r$ at every point of $\operatorname{Spec}k$. The assertion is that there exist $r$ morphisms $a_i\colon\operatorname{Spec}k\to\mathcal C$, indexed by $i\in\mathrm{Fin}\,r$, each satisfying $a_i$ followed by $f$ equals $x$, such that $D.I$ is the product over $i$ of the kernel ideal sheaves of the graph sections $\operatorname{graphOver}f\,a_i\colon\operatorname{Spec}k\to\mathcal C\times_S\operatorname{Spec}k$, the graph being the morphism induced by $a_i$ and $\mathrm{id}_{\operatorname{Spec}k}$ into the pullback. In short, $D=a_0+\dots+a_{r-1}$ in the `prodKerGraph` notation.
--
--   This is the classical fact that on a smooth curve over an algebraically closed field every relative effective divisor of degree $r$ splits as a sum of $r$ rational points; it is the converse, at geometric points, of the statement that sums of sections are divisors. It is used in the local analysis of relative Picard functors, for instance in the fibrewise computations of twist modules and of charts trivialising the relevant $H^1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {k : Type u} [Field k] [IsAlgClosed k] {x : Spec (CommRingCat.of k) ⟶ S}
    {r : ℕ} (D : RelEffCartierDiv f r x) :
    ∃ (a : Fin r → (Spec (CommRingCat.of k) ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = x),
      D.I = prodKerGraph f a ha := by sorry
