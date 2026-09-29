-- Prove2me | Theorems.Thm_AutomorphicForm_archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex
-- name    : AutomorphicForm.archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/07b4c632-dbfb-5fde-b3f4-8054b46c8baf
-- title:
--   Complex-place Casimirs commute with right convolution by test functions
-- statement:
--   Let $K$ be a number field, $w$ an infinite place of $K$ with $w$ complex, and $x\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ a function on the adelic group `AdelicGL2 (𝓞 K) K`. Assume: $x$ is continuous; $x$ satisfies `IsArchSmoothAtComplex hw`, i.e. for every $g$ the map $e\mapsto x(g\cdot \mathrm{archComplexLiftAt}\,e)$ is $C^\infty$ over $\mathbb{R}$ on the set of $2\times 2$ complex matrices $e$ with $\det e\neq 0$, where the lift places $e$ at $w$; for each of the six directions $d\in\{H,E,F^-,iH,iE,iF^-\}$ the function $\mathrm{archDerivAtComplex}\,d\,x$, given by $g\mapsto \frac{d}{dt}x(g\cdot \mathrm{archFlowAtComplex}\,d\,t)|_{t=0}$, is continuous; and likewise all second such derivatives $\mathrm{archDerivAtComplex}\,d\,(\mathrm{archDerivAtComplex}\,d'\,x)$ are continuous. Then for every $f\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and every archimedean type family $tys$ (a number $\mathrm{card}(v)$ of types $\mathrm{rep}(v,i)\in\mathrm{ArchRepAt}\,K\,v$ for each infinite place $v$) such that $f$ is a factorizable test function, i.e. $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ of compact support and given by a $C^\infty$ function of the mixed-space matrix entries and $f_{\mathrm{fin}}$ locally constant of compact support, and such that $f$ is archimedean bi-finite for $tys$ (the function $g\mapsto f(g^{-1})$ lies in `archCutSubmodule K tys` and $f$ lies in `archDualCutSubmodule K tys`), the right convolution $(x*f)(g)=\int x(gy)f(y)\,dy$ against the adelic Haar measure on $\mathrm{GL}_2$ again satisfies `IsArchSmoothAtComplex hw`, has continuous first and second derivatives along all six directions, and satisfies $\Omega_w(x*f)=(\Omega_w x)*f$ and $\overline{\Omega}_w(x*f)=(\overline{\Omega}_w x)*f$, where $\Omega_w=\mathrm{archCasimirAtComplex}$ is $-\bigl(\tfrac14\partial_H\partial_H-\tfrac12\partial_H+\partial_E\partial_{F^-}\bigr)$ with $\partial_X=\tfrac12(D_X-iD_{iX})$, and $\overline{\Omega}_w=\mathrm{archCasimirBarAtComplex}$ is the same expression in $\bar\partial_X=\tfrac12(D_X+iD_{iX})$.
--
--   This is the centrality of the two Casimir elements of $\mathfrak{gl}_2(\mathbb{C})$ at a complex place, expressed as the commutation of $\Omega_w$ and $\overline{\Omega}_w$ with the right convolution action of factorizable test functions, together with the regularity of the convolved function. It is used in the treatment of Casimir eigenvalues under right translation and convolution, which feeds the analysis of the archimedean components of automorphic representations at complex places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    ∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (tys : AutomorphicForm.ArchTypeFamily K),
        IsFactorizableTestFn K f → IsArchBiFinite K tys f →
        IsArchSmoothAtComplex hw (rightConv K x f) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightConv K x f))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (rightConv K x f)))) ∧
        archCasimirAtComplex hw (rightConv K x f) = rightConv K (archCasimirAtComplex hw x) f ∧
        archCasimirBarAtComplex hw (rightConv K x f) = rightConv K (archCasimirBarAtComplex hw x) f := by sorry
