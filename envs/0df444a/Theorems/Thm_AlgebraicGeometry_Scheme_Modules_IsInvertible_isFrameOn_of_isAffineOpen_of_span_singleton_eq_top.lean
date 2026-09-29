-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_of_isAffineOpen_of_span_singleton_eq_top
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.isFrameOn_of_isAffineOpen_of_span_singleton_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/f7422330-8589-575e-98c5-463b3fc93d44
-- title:
--   Generating section of an invertible sheaf on an affine open is a frame
-- statement:
--   Let $X$ be a scheme and let $L$ be an $\mathcal O_X$-module (an object of `X.Modules`) which is invertible in the sense of the project's predicate `Scheme.Modules.IsInvertible`: for every point $x$ of $X$ there is an open $U \ni x$ such that the pullback of $L$ along the inclusion $U.\iota$ is isomorphic to the unit module $\mathcal O_U$ on the scheme $U$. Let $U$ be an open subset of $X$ which is an affine open, and let $m \in \Gamma(L, U)$ be a section whose $\Gamma(X, U)$-submodule span, $\operatorname{span}_{\Gamma(X,U)}\{m\}$, is all of $\Gamma(L, U)$. The conclusion is `Scheme.Modules.IsFrameOn m U`, i.e. for every open $W$ with $W \le U$ (the definition asks for $W$ contained in the domain of the section and in the given open, both here equal to $U$) the map
--   $$\Gamma(X, W) \longrightarrow \Gamma(L, W), \qquad g \mapsto g \cdot \bigl(m|_W\bigr),$$
--   where $m|_W$ denotes the image of $m$ under the restriction map of the presheaf of $L$ along $W \le U$, is bijective.
--
--   This is the standard statement that a section generating an invertible module over an affine open trivialises it there, multiplication by $m$ giving an isomorphism $\mathcal O_U \xrightarrow{\ \sim\ } L|_U$; in the project the conclusion is packaged as the predicate `IsFrameOn`, which records bijectivity of multiplication by the restrictions of $m$ on all smaller opens. It is used in the construction of trivialisations of invertible modules, namely by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_pullback_iso_of_forall_bijective_smul_res_of_affHom_pushforward`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_pullback_iso_of_forall_bijective_smul_res_of_affHom_pushforward), within the treatment of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_of_isAffineOpen_of_span_singleton_eq_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.isFrameOn_of_isAffineOpen_of_span_singleton_eq_top
    {X : Scheme.{u}} {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    {U : X.Opens} (hU : IsAffineOpen U) (m : Γ(L, U))
    (hm : Submodule.span Γ(X, U) {m} = ⊤) :
    Scheme.Modules.IsFrameOn m U := by sorry
