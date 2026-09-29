-- Prove2me | Theorems.Thm_AutomorphicForm_archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt
-- name    : AutomorphicForm.archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/c5696104-7337-5217-adcb-a071d31f24d4
-- title:
--   Casimir at a real place commutes with right convolution
-- statement:
--   Let $K$ be a number field, $w$ an infinite place of $K$ and $hw$ a proof that $w$ is real, and let $x \colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous and smooth at $w$ in the sense of `IsArchSmoothAt`, i.e. for every $g$ the map sending a real $2\times 2$ matrix $e$ to $x(g \cdot \mathrm{archRealLiftAt}\, e)$ is $C^\infty$ on the locus $\det e \neq 0$, where $\mathrm{archRealLiftAt}$ places an invertible real matrix in the $w$-component. Assume moreover that for each of the three directions $d \in \{H, E, F^-\}$ the derivative $\mathrm{archDerivAt}\,d\,x$, given by $g \mapsto \frac{d}{dt}x(g \cdot \exp_w(tX_d))|_{t=0}$, is continuous, and likewise for all second derivatives $\mathrm{archDerivAt}\,d\,(\mathrm{archDerivAt}\,d'\,x)$. Then for every $f \colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ and every archimedean type family $tys$ (finitely many representations of the relevant isometry subgroup at each infinite place) such that $f$ is a factorizable test function, namely $f(g) = f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ compactly supported and induced by a $C^\infty$ function of the mixed-space matrix entries and $f_{\mathrm{fin}}$ locally constant of compact support, and such that $f$ is bi-finite for $tys$, i.e. $g \mapsto f(g^{-1})$ lies in the cut submodule $\mathrm{archCutSubmodule}\,tys$ and $f$ lies in $\mathrm{archDualCutSubmodule}\,tys$: the right convolution $(x * f)(g) = \int x(gy)f(y)\,dy$ against the adelic Haar measure is again smooth at $w$, its first and second archimedean derivatives in all directions are continuous, and $\Omega_w(x * f) = (\Omega_w x) * f$, where $\Omega_w\varphi = -\bigl(\tfrac14 D_H D_H \varphi - \tfrac12 D_H\varphi + D_E D_{F^-}\varphi\bigr)$ is `archCasimirAt`.
--
--   This is the centrality of the Casimir element of $U(\mathfrak{gl}_2)$ in adelic form: the Casimir operator at a real place commutes with right convolution by bi-finite factorizable test functions, and right convolution preserves the regularity conditions under which that operator is defined. It is used, via [`AutomorphicForm.archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt`](thm.html#AutomorphicForm.archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt), to show that Casimir eigenspaces of automorphic functions are stable under the convolution action of the Hecke algebra at the archimedean places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    ∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (tys : AutomorphicForm.ArchTypeFamily K),
        IsFactorizableTestFn K f → IsArchBiFinite K tys f →
        IsArchSmoothAt hw (rightConv K x f) ∧
        (∀ d : ArchDir, Continuous (archDerivAt hw d (rightConv K x f))) ∧
        (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightConv K x f)))) ∧
        archCasimirAt hw (rightConv K x f) = rightConv K (archCasimirAt hw x) f := by sorry
