-- Prove2me | Theorems.Thm_AutomorphicForm_archCasimirAtComplex_rightConv_eq_smul_of_archCasimirAtComplex_eq_smul_of_isArchSmoothAtComplex_of_isFactorizableTestFn
-- name    : AutomorphicForm.archCasimirAtComplex_rightConv_eq_smul_of_archCasimirAtComplex_eq_smul_of_isArchSmoothAtComplex_of_isFactorizableTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/3905bb22-902c-5c53-a0d2-adea48a91f1d
-- title:
--   Right convolution preserves Casimir eigenvalues at a complex place
-- statement:
--   Let $K$ be a number field and $w$ a complex infinite place of $K$, with $hw$ witnessing $w.\mathrm{IsComplex}$, and let $\varphi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $K$. Assume: $\varphi$ is continuous; $\varphi$ is smooth at $w$ in the sense of `IsArchSmoothAtComplex`, i.e. for every $g$ the map $e \mapsto \varphi(g\cdot\mathrm{archComplexLiftAt}\,hw\,e)$ on $2\times 2$ complex matrices is $C^\infty$ (over $\mathbb{R}$) on the set where $\det e \neq 0$; for each of the six directions $d$ in `ArchDirComplex` (namely `H`, `E`, `Fm`, `iH`, `iE`, `iFm`, indexing one-parameter flows $\mathrm{archFlowAtComplex}\,hw\,d\,t$ placed at $w$) the first derivative $\mathrm{archDerivAtComplex}\,hw\,d\,\varphi$, given by $g \mapsto \frac{d}{dt}\varphi(g\cdot \mathrm{archFlowAtComplex}\,hw\,d\,t)|_{t=0}$, is continuous, and likewise all second derivatives $\mathrm{archDerivAtComplex}\,hw\,d\,(\mathrm{archDerivAtComplex}\,hw\,d'\,\varphi)$ are continuous. Assume further that for scalars $\mathrm{lam},\mathrm{lam}' \in \mathbb{C}$ one has $\mathrm{archCasimirAtComplex}\,hw\,\varphi = \mathrm{lam}\cdot\varphi$ and $\mathrm{archCasimirBarAtComplex}\,hw\,\varphi = \mathrm{lam}'\cdot\varphi$, where the two operators are $-\bigl(\tfrac14 \partial_H\partial_H - \tfrac12 \partial_H + \partial_E\partial_{Fm}\bigr)$ formed from the holomorphic combinations $\partial_d = \tfrac12(\mathrm{archDerivAtComplex}\,hw\,d - i\,\mathrm{archDerivAtComplex}\,hw\,(id))$ and, respectively, from the antiholomorphic combinations $\bar\partial_d = \tfrac12(\mathrm{archDerivAtComplex}\,hw\,d + i\,\mathrm{archDerivAtComplex}\,hw\,(id))$. Finally let $f$ be a factorizable test function, i.e. $f(g) = f_\infty(g_\infty)\,f_{\mathrm{fin}}(g_{\mathrm{fin}})$ where $f_\infty$ on $\mathrm{GL}_2$ of the infinite adeles is compactly supported and arises as a globally $C^\infty$ function of the archimedean matrix entries, and $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adeles is locally constant with compact support. The conclusion is threefold: the right convolution $\mathrm{rightConv}\,K\,\varphi\,f$, defined by $g \mapsto \int \varphi(gx) f(x)\,d\mu(x)$ for the adelic Haar measure on $\mathrm{GL}_2$ of the adele ring, is again smooth at $w$ in the above sense, and it is again an eigenfunction of both operators with the same eigenvalues, $\mathrm{archCasimirAtComplex}\,hw\,(\varphi * f) = \mathrm{lam}\cdot(\varphi*f)$ and $\mathrm{archCasimirBarAtComplex}\,hw\,(\varphi*f) = \mathrm{lam}'\cdot(\varphi*f)$.
--
--   This records that the two Casimir operators attached to a complex place commute with right convolution by a factorizable test function, so that convolution acts within a joint Casimir eigenspace; it is the complex-place counterpart of the corresponding statement at a real place. It is used in the derivation of norm bounds for convolution operators on isotypic subspaces of cusp forms with prescribed Casimir eigenvalues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archCasimirAtComplex_rightConv_eq_smul_of_archCasimirAtComplex_eq_smul_of_isArchSmoothAtComplex_of_isFactorizableTestFn.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.archCasimirAtComplex_rightConv_eq_smul_of_archCasimirAtComplex_eq_smul_of_isArchSmoothAtComplex_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ) (hs : IsArchSmoothAtComplex hw φ)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d φ))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' φ)))
    (lam lam' : ℂ) (hΩ : archCasimirAtComplex hw φ = lam • φ) (hΩb : archCasimirBarAtComplex hw φ = lam' • φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f) :
    IsArchSmoothAtComplex hw (rightConv K φ f) ∧
      archCasimirAtComplex hw (rightConv K φ f) = lam • rightConv K φ f ∧
      archCasimirBarAtComplex hw (rightConv K φ f) = lam' • rightConv K φ f := by sorry
