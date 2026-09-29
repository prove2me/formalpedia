-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial
-- name    : AlgebraicGeometry.Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/23d43ce4-ea77-5332-8cef-2b02c6698890
-- title:
--   Surjectivity on affine sections when the kernel is locally trivial
-- statement:
--   Let $X$ be a scheme and let $S$ be a short complex $S_1 \xrightarrow{f} S_2 \xrightarrow{g} S_3$ in the category `X.Modules` of sheaves of modules over the structure sheaf of $X$, assumed short exact, i.e. $f$ is a monomorphism, $g$ is an epimorphism and the complex is exact. Assume further that $S_1$ is locally trivial in the following elementwise sense: for every point $p$ of $X$ there is an open $W \subseteq X$ with $p \in W$ such that the pullback of $S_1$ along the open immersion $W \hookrightarrow X$ is isomorphic, as a sheaf of modules on $W$, to the unit object for the structure sheaf of $W$ (the isomorphism being asserted only to exist, through `Nonempty`); that is, $S_1$ is an invertible sheaf. Let $U$ be an open of $X$ which is an affine open. Then the induced map on sections over $U$, $g_U \colon \Gamma(S_2, U) \to \Gamma(S_3, U)$, is surjective.
--
--   This is the invertible-sheaf case of Serre's vanishing theorem on affine schemes, $H^1(U, S_1) = 0$ for quasi-coherent $S_1$ and $U$ affine, in the concrete form that sections of an epimorphism lift over affine opens; combined with left exactness of the sections functor it gives exactness of $0 \to \Gamma(S_1,U) \to \Gamma(S_2,U) \to \Gamma(S_3,U) \to 0$. It is used in the extension of this surjectivity to unions of affine opens and in the computations of Euler characteristics of invertible sheaves on curves obtained by gluing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial
    {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj S.X₁ ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (S.g.app U) := by sorry
