-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_basis_one
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_basis_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/1579c277-4ec9-51b9-bb79-d332d8813dcf
-- title:
--   Local generating section of an invertible sheaf of modules
-- statement:
--   Let $X$ be a scheme and let $L$ be a sheaf of modules over the structure sheaf of $X$ (an object of `X.Modules`) which is invertible in the sense of the project's predicate `Scheme.Modules.IsInvertible`: for every point of $X$ there is an open neighbourhood $U$ such that the pullback of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic, as a sheaf of modules on $U$, to the unit sheaf of modules of $U$ (the structure sheaf viewed as a module over itself). Let $x$ be a point of $X$. Then there exist an open subset $V \subseteq X$ with $x \in V$ and a section $u \in \Gamma(L, V)$ with the following property: for every open $W$ with $W \le V$ the $\Gamma(X, W)$-module $\Gamma(L, W)$ admits a basis indexed by `Fin 1` whose unique member is the restriction of $u$ to $W$, that is, the image of $u$ under $L$'s presheaf map along the opposite of the inclusion $W \le V$. Equivalently, $u$ is a local frame: on every open subset of $V$ its restriction freely generates the sections of $L$ over the structure-sheaf sections.
--
--   This is the translation of invertibility (local triviality) of a sheaf of modules into the existence of a local generating section, or local frame, whose restrictions are bases of the section modules over all smaller opens. It is used for local computations with line bundles on sections, namely in [`AlgebraicGeometry.Scheme.Modules.epi_whiskerRight_wedgeVec_of_shortExact`](thm.html#AlgebraicGeometry.Scheme.Modules.epi_whiskerRight_wedgeVec_of_shortExact) and in [`AlgebraicGeometry.Scheme.Modules.exists_pullbackSection_dual_det_eq_zero_iff_not_isIso`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_pullbackSection_dual_det_eq_zero_iff_not_isIso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_basis_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_basis_one
    {X : Scheme.{u}} {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) (x : X) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ u : Γ(L, V), ∀ (W : X.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin 1) Γ(X, W) Γ(L, W), b 0 = L.presheaf.map (homOfLE hW).op u := by sorry
