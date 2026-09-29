-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isFrameOn_sheafificationAdjunction_unit_iotaMulti
-- name    : AlgebraicGeometry.Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/204a35f1-2549-52ba-91e3-713ea32854c2
-- title:
--   Top wedge of a local basis frames detₙ M
-- statement:
--   Let $X$ be a scheme, $n$ a natural number, $M$ a sheaf of $\mathcal{O}_X$-modules on $X$, $U$ an open subset of $X$, and $e : \mathrm{Fin}\,n \to \Gamma(M,U)$ a family of $n$ sections of $M$ over $U$. Assume that for every open $W$ with $W \le U$ there is a basis of the $\Gamma(X,W)$-module $\Gamma(M,W)$ indexed by $\mathrm{Fin}\,n$ whose $i$-th member is the restriction of $e_i$ to $W$. Form the wedge $\mathrm{ιMulti}$ of $e$, namely $e_0 \wedge \dots \wedge e_{n-1}$ in the $n$-th exterior power of $\Gamma(M,U)$ over $\Gamma(X,U)$, which is the value at $U$ of the presheaf of modules `Scheme.Modules.presheafExteriorPower X n` applied to the underlying presheaf of $M$, and let $\omega \in \Gamma(\det{}_n M, U)$ be its image under the component at $U$ of the unit of the sheafification adjunction, where $\det{}_n M$ is by definition the sheafification of that sectionwise exterior power. The conclusion is `Scheme.Modules.IsFrameOn` for $\omega$ on $U$, i.e. for every open $W \le U$ the map $\Gamma(X,W) \to \Gamma(\det{}_n M, W)$ sending $g$ to $g$ times the restriction of $\omega$ to $W$ is bijective.
--
--   This identifies the top wedge of a local basis as a free generator (a "frame") of the determinant sheaf $\det_n M = \bigwedge^n M$ over the open set on which the basis exists, so that $\det_n M$ is invertible there with an explicit trivialising section. It is used in the construction of frames for norm modules and in the comparison of frames under pullback along a morphism of schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isFrameOn_sheafificationAdjunction_unit_iotaMulti.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti
    {X : Scheme.{u}} {n : ℕ} {M : X.Modules} {U : X.Opens} (e : Fin n → Γ(M, U))
    (he : ∀ (W : X.Opens) (hW : W ≤ U), ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W),
      ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i)) :
    Scheme.Modules.IsFrameOn (M := Scheme.Modules.det n M)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((Scheme.Modules.presheafExteriorPower X n).obj M.val)).app (op U)
        (show ((Scheme.Modules.presheafExteriorPower X n).obj M.val).obj (op U) from
          exteriorPower.ιMulti Γ(X, U) n e))
      U := by sorry
