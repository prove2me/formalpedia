-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_det_iso_det_pullback
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_pullback_det_iso_det_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/820e0d03-2b5d-5af5-ab6f-790b1921dfe3
-- title:
--   Determinant commutes with pullback for locally free sheaves
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe), let $\psi \colon X \to Y$ be a morphism of schemes, let $n$ be a natural number, and let $E$ be a sheaf of modules on $Y$ which is locally free of rank $n$ in the sense of the project's predicate `IsLocallyFreeOfRank`: every point of $Y$ lies in an open $U$ such that the pullback of $E$ along the inclusion $U \hookrightarrow Y$ admits an isomorphism with the free sheaf of modules on the index type $\mathrm{ULift}(\mathrm{Fin}\ n)$. Here $\det_n$ denotes the operation `Scheme.Modules.det`, namely the value of the functor `exteriorPower` at $n$: pass to the underlying presheaf of modules, form the sectionwise $n$-th exterior power presheaf, and sheafify over the structure sheaf of rings. The conclusion asserts that the type of isomorphisms of sheaves of $\mathcal{O}_X$-modules between $\psi^{*}(\det_n E)$ and $\det_n(\psi^{*}E)$ is nonempty, where $\psi^{*}$ is `Scheme.Modules.pullback`. Thus only the existence of such an isomorphism is asserted, with no chosen isomorphism and no naturality in $\psi$ or in $E$.
--
--   This is the compatibility of exterior powers, and in particular of determinant line bundles, with base change, in the form $\psi^{*}\bigwedge^{n}E \cong \bigwedge^{n}\psi^{*}E$ for $E$ locally free of rank $n$. It is used for the behaviour under base change of the theta bundle of a relative Picard construction and of norm modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_det_iso_det_pullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_det_iso_det_pullback
    {X Y : Scheme.{u}} (ψ : X ⟶ Y) (n : ℕ) {E : Y.Modules} (hE : Scheme.Modules.IsLocallyFreeOfRank n E) :
    Nonempty ((Scheme.Modules.pullback ψ).obj (Scheme.Modules.det n E) ≅
      Scheme.Modules.det n ((Scheme.Modules.pullback ψ).obj E)) := by sorry
