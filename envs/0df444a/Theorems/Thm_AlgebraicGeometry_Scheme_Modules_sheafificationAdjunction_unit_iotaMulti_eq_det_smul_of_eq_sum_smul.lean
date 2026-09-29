-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul
-- name    : AlgebraicGeometry.Scheme.Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/8bef52d2-3292-5431-887a-8fec7905aa50
-- title:
--   Wedge of a linearly transformed family scales by the determinant
-- statement:
--   Let $X$ be a scheme, $M$ a sheaf of $\mathcal O_X$-modules on $X$ (an object of `X.Modules`), $V$ an open subset of $X$ and $d$ a natural number. Let $f, f' : \mathrm{Fin}\,d \to \Gamma(M,V)$ be two families of sections of $M$ over $V$ and let $a$ be a $d \times d$ matrix with entries in $\Gamma(X,V)$ such that $f'_j = \sum_i a_{ij}\, f_i$ for every index $j$. Form, over $V$, the exterior-power element $\mathrm{ιMulti}$ of $\bigwedge^d_{\Gamma(X,V)}\Gamma(M,V)$, i.e. the section of the presheaf `Scheme.Modules.presheafExteriorPower X d` applied to the underlying presheaf of modules `M.val` — the presheaf whose value on an open $U$ is the $d$-th exterior power of $\Gamma(M,U)$ over $\Gamma(X,U)$ — and push it into $\Gamma(\mathrm{det}\,d\,M, V)$ along the component at $V$ of the unit of the sheafification adjunction for presheaves of modules over $\mathcal O_X$. The theorem asserts that the image of the element built from $f'$ equals $\det(a)$ times the image of the element built from $f$, equality in the module of sections $\Gamma(\mathrm{det}\,d\,M,V)$.
--
--   This is the usual transformation rule $f'_1\wedge\dots\wedge f'_d = \det(a)\,(f_1\wedge\dots\wedge f_d)$, stated for the sheafified $d$-th exterior power (determinant) of a sheaf of modules and for the distinguished sections obtained by sheafifying wedge products of global-on-$V$ sections; no freeness or basis hypothesis is imposed and $d = 0$ is allowed. It is used when local frames of determinant and norm modules are compared and glued, for instance in the construction of frames for the norm module along a closed immersion and in the transfer of frame data between an open and its preimage.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesNormModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul
    {X : Scheme.{u}} {M : X.Modules} {V : X.Opens} {d : ℕ} (f f' : Fin d → Γ(M, V))
    (a : Matrix (Fin d) (Fin d) Γ(X, V)) (h : ∀ j, f' j = ∑ i, a i j • f i) :
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower X d).obj M.val)).app (op V)
      (show ((Scheme.Modules.presheafExteriorPower X d).obj M.val).obj (op V) from exteriorPower.ιMulti Γ(X, V) d f') :
      Γ(Scheme.Modules.det d M, V)) =
    a.det • (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower X d).obj M.val)).app (op V)
      (show ((Scheme.Modules.presheafExteriorPower X d).obj M.val).obj (op V) from exteriorPower.ιMulti Γ(X, V) d f) :
      Γ(Scheme.Modules.det d M, V)) := by sorry
