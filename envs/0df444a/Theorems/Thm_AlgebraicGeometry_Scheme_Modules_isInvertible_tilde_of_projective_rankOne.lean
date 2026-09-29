-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_tilde_of_projective_rankOne
-- name    : AlgebraicGeometry.Scheme.Modules.isInvertible_tilde_of_projective_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/69b3cc48-b00e-51c0-bd37-6347d7318f36
-- title:
--   Rank-one finite projective modules give invertible sheaves on Spec R
-- statement:
--   Let $R$ be a commutative ring and let $P$ be an $R$-module which is finite (finitely generated) and projective over $R$, and suppose that for every field $K$ equipped with an $R$-algebra structure the base change $K \otimes_R P$ has $K$-dimension $1$, i.e. $\operatorname{finrank}_K(K \otimes_R P) = 1$ for all such $K$. The conclusion is that the quasi-coherent sheaf of modules $\widetilde{P}$ associated with $P$ on $\operatorname{Spec} R$ satisfies the project's predicate `Scheme.Modules.IsInvertible`, which unfolds to: for every point $x$ of $\operatorname{Spec} R$ there is an open subscheme $U$ of $\operatorname{Spec} R$ with $x \in U$ such that the pullback of $\widetilde{P}$ along the open immersion $U \hookrightarrow \operatorname{Spec} R$ is isomorphic, as a sheaf of modules over the structure sheaf of $U$, to the unit object (the structure sheaf viewed as a module over itself); the existence of such an isomorphism is asserted as nonemptiness of the type of isomorphisms, not as a chosen one.
--
--   This is the module-to-sheaf direction of the affine dictionary between finite projective $R$-modules of constant rank one and line bundles on $\operatorname{Spec} R$, and it is the standard way invertible sheaves on affine schemes are produced in the formalisation. It is used in the construction of descent data for invertible modules along faithfully flat surjective affine morphisms, which enters the treatment of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_tilde_of_projective_rankOne.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.isInvertible_tilde_of_projective_rankOne
    {R : CommRingCat.{u}} (P : ModuleCat.{u} R) [Module.Finite R P] [Module.Projective R P]
    (hrk : ∀ (K : Type u) [Field K] [Algebra R K], Module.finrank K (K ⊗[R] P) = 1) :
    Scheme.Modules.IsInvertible (tilde P) := by sorry
