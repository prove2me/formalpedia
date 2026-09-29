-- Prove2me | Theorems.Thm_AutomorphicForm_archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt
-- name    : AutomorphicForm.archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/d97d2bc7-0338-57fe-8963-c4557500cc46
-- title:
--   Casimir at a real place: translation and convolution invariance
-- statement:
--   Let $K$ be a number field and $w$ an infinite place of $K$ with $w$ real, and let $x \colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous and archimedean-smooth at $w$, i.e. for every $g$ the function $e \mapsto x(g \cdot \mathrm{archRealLiftAt}(e))$ is $C^\infty$ on the set of real $2\times2$ matrices of nonzero determinant, where a matrix is placed at $w$ via the real embedding. Assume further that for each of the three directions $d \in \{H, E, F\}$ the derivative $\mathrm{archDerivAt}\,d\,x$, given by $g \mapsto \frac{d}{dt}x(g\cdot\exp(tX_d))|_{t=0}$ with the flow placed at $w$, is continuous, and that all second derivatives $\mathrm{archDerivAt}\,d\,(\mathrm{archDerivAt}\,d'\,x)$ are continuous. Write $\Omega_w = -\bigl(\tfrac14 D_H D_H - \tfrac12 D_H + D_E D_F\bigr)$ for `archCasimirAt`. Then two assertions hold simultaneously. First, for every infinite place $w'$ of $K$ and every $k$ in the subgroup `rowIsometrySubgroup₀` of $\mathrm{GL}_2(K_{w'})$, the right translate $y \mapsto x(y \cdot \iota(k))$ by the image $\iota(k) = \mathrm{rowIsometryInclAt₀}\,K\,w'\,k$ is again archimedean-smooth at $w$ with continuous first and second derivatives in all directions, and $\Omega_w$ commutes with this translation. Second, for every $f \colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ and every family of archimedean types `tys` (a number $\mathrm{card}(v)$ of finite-dimensional representations of `rowIsometrySubgroup₀` at each infinite place $v$) such that $f$ is a factorizable test function — $f(g) = f_\infty(g_\infty) f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ compactly supported and given by a $C^\infty$ function of the archimedean matrix entries, and $f_{\mathrm{fin}}$ locally constant with compact support — and satisfies `IsArchBiFinite` for `tys`, the right convolution $(x * f)(g) = \int x(g y) f(y)\,dy$ against the adelic Haar measure on $\mathrm{GL}_2$ is archimedean-smooth at $w$ with continuous first and second derivatives in all directions, and $\Omega_w(x*f) = (\Omega_w x) * f$.
--
--   This packages the two stability properties of the Casimir operator at a real place — invariance under right translation by the row-isometry groups at all infinite places (Ad-invariance at $w$ itself, trivial commutation elsewhere) and commutation with right convolution by bi-finite test functions — in the single form needed downstream. It is used in the proofs that a cuspidal constituent has a Casimir eigenvalue at each real place, where the eigenspace must be shown to be again stable under the relevant actions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt.lean

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

theorem AutomorphicForm.archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    (∀ (w' : InfinitePlace K) (k : rowIsometrySubgroup₀ w'.Completion),
        IsArchSmoothAt hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) ∧
        (∀ d : ArchDir, Continuous (archDerivAt hw d (rightTranslate K (rowIsometryInclAt₀ K w' k) x))) ∧
        (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d'
          (rightTranslate K (rowIsometryInclAt₀ K w' k) x)))) ∧
        archCasimirAt hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirAt hw x)) ∧
    (∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (tys : AutomorphicForm.ArchTypeFamily K),
        IsFactorizableTestFn K f → IsArchBiFinite K tys f →
        IsArchSmoothAt hw (rightConv K x f) ∧
        (∀ d : ArchDir, Continuous (archDerivAt hw d (rightConv K x f))) ∧
        (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightConv K x f)))) ∧
        archCasimirAt hw (rightConv K x f) = rightConv K (archCasimirAt hw x) f) := by sorry
