-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_of_bijective_app_of_le_opensRange
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/eb3c87e9-1a0e-567d-a828-b8b984364b89
-- title:
--   Open immersion: π: L→ f_*M bijective on small opens gives f^*L≅ M
-- statement:
--   Let $f\colon Y\to X$ be a morphism of schemes (in a fixed universe) which is an open immersion, let $M$ be a module on $Y$ and $L$ a module on $X$, in the sense of the categories $Y.\mathrm{Modules}$ and $X.\mathrm{Modules}$ of quasi-coherent-style sheaves of modules used here, and let $\pi\colon L\to f_*M$ be a morphism in $X.\mathrm{Modules}$, where $f_* =$ `Scheme.Modules.pushforward f`. Assume that for every open $U$ of $X$ with $U \le f.\mathrm{opensRange}$, i.e. $U$ contained in the open image of $f$, the induced map on sections $\pi.\mathrm{app}\,U \colon \Gamma(U,L) \to \Gamma(U, f_*M)$ is bijective. The conclusion is that the type of isomorphisms $(f^*L) \cong M$ in $Y.\mathrm{Modules}$ is nonempty, where $f^* =$ `Scheme.Modules.pullback f`; that is, the pullback of $L$ along $f$ is isomorphic to $M$. Note that the conclusion asserts nonemptiness of the set of isomorphisms rather than exhibiting a designated one, and that no condition whatsoever is imposed on the sections of $L$ over opens not contained in the image of $f$.
--
--   This is the standard statement that, along an open immersion, a module $L$ on the target together with a map to $f_*M$ which is bijective on sections over opens inside the image restricts to $M$; in other words $L$ may be any extension of $M$ across $X$. It is used in the analysis of invertible sheaves and their sections over two-chart affine open covers, in [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_isInvertible_sectionsOf_equiv_of_projective`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_isInvertible_sectionsOf_equiv_of_projective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_of_bijective_app_of_le_opensRange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (M : Y.Modules) (L : X.Modules)
    (π : L ⟶ (Scheme.Modules.pushforward f).obj M)
    (hπ : ∀ U : X.Opens, U ≤ f.opensRange → Function.Bijective (π.app U)) :
    Nonempty ((Scheme.Modules.pullback f).obj L ≅ M) := by sorry
