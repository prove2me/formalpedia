-- Prove2me | Theorems.Thm_AlgebraicGeometry_etale_of_isFinite_of_isReduced_of_perfectField
-- name    : AlgebraicGeometry.etale_of_isFinite_of_isReduced_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/5e2ffedc-30ce-536c-bdf7-14663d3f493b
-- title:
--   Finite reduced schemes over a perfect field are étale
-- statement:
--   Let $K$ be a perfect field (a field in the universe $u$ with the `PerfectField` property), and let $B$ be a scheme in the universe $u$. Let $g \colon B \to \operatorname{Spec} K$ be a morphism of schemes to the spectrum of $K$, regarded as the spectrum of the commutative ring $K$, and assume that $g$ is a finite morphism (`IsFinite`) and that $B$ is a reduced scheme (`IsReduced`). The conclusion is that $g$ is étale in the sense of `Etale`, that is, flat and formally unramified and locally of finite presentation. No separability or smoothness hypothesis on $B$ beyond reducedness is imposed; perfectness of $K$ is what makes reducedness suffice.
--
--   This is the standard criterion identifying the finite étale $K$-schemes among the finite $K$-schemes when $K$ is perfect: a finite reduced scheme over a perfect field is automatically étale over it (compare EGA IV₄ 17.6.2). It is used in the construction of fake elliptic curves in the Čerednik–Drinfel'd part of the development, where finiteness and reducedness of a scheme of points over a field are available and étaleness of the structure morphism is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_etale_of_isFinite_of_isReduced_of_perfectField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.etale_of_isFinite_of_isReduced_of_perfectField
    {K : Type u} [Field K] [PerfectField K]
    {B : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of K)) [IsFinite g] [IsReduced B] : Etale g := by sorry
