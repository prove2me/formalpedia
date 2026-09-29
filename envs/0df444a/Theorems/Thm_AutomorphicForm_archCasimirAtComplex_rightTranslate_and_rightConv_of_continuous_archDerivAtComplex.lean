-- Prove2me | Theorems.Thm_AutomorphicForm_archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex
-- name    : AutomorphicForm.archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/46210eb0-2444-5fa6-8d76-e4c65a9c708e
-- title:
--   Casimir operators at a complex place commute with translation and convolution
-- statement:
--   Let $K$ be a number field and $w$ an infinite place of $K$ with $w$ complex, and let $x \colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be a continuous function which is `IsArchSmoothAtComplex` for $w$, i.e. for every $g$ the map sending a $2\times 2$ complex matrix $e$ to $x(g \cdot \mathtt{archComplexLiftAt}\,e)$, where the matrix is placed in the $w$-component, is real $C^\infty$ on the locus $\det e \neq 0$. Assume moreover that for each of the six directions $d \in \{H,E,F^-,iH,iE,iF^-\}$ the derivative $\mathtt{archDerivAtComplex}\,d\,x$, given at $g$ by $\frac{d}{dt}x(g \cdot \exp_w(td))|_{t=0}$, is continuous, and likewise for all second derivatives $\mathtt{archDerivAtComplex}\,d\,(\mathtt{archDerivAtComplex}\,d'\,x)$. Write $\partial_d = \tfrac12(D_{d} - i D_{id})$, $\bar\partial_d = \tfrac12(D_{d} + i D_{id})$ and $\Omega_w\varphi = -\bigl(\tfrac14 \partial_H\partial_H\varphi - \tfrac12\partial_H\varphi + \partial_E\partial_{F^-}\varphi\bigr)$, with $\bar\Omega_w$ the same expression in the $\bar\partial$'s. The conclusion is a conjunction of two statements. First, for every infinite place $w'$ of $K$ and every $k$ in the group `rowIsometrySubgroup₀` of $\mathrm{GL}_2(K_{w'})$, the right translate $\mathtt{rightTranslate}\,(\mathtt{rowIsometryInclAt₀}\,w'\,k)\,x$, namely $y \mapsto x(y\,\iota_{w'}(k))$, again satisfies the smoothness condition at $w$ and the continuity of its first and second archimedean derivatives, and both Casimir operators commute with this translation: $\Omega_w(R_k x) = R_k(\Omega_w x)$ and $\bar\Omega_w(R_k x) = R_k(\bar\Omega_w x)$. Second, for every $f \colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ and every archimedean type family $\mathtt{tys}$ (a number of types $\mathtt{card}\,w'$ together with representations $\mathtt{rep}\,w'$ at each infinite place $w'$) such that $f$ is a factorizable test function, i.e. $f(g) = f_\infty(g_\infty) f_{\mathrm{fin}}(g_{\mathrm{fin}})$ for an archimedean test factor $f_\infty$ and a finite test factor $f_{\mathrm{fin}}$, and such that $f$ is archimedean bi-finite for $\mathtt{tys}$ (that is, $g \mapsto f(g^{-1})$ lies in the archimedean cut submodule and $f$ in the dual cut submodule of that family), the right convolution $(\mathtt{rightConv}\,x\,f)(g) = \int x(gy) f(y)\,dy$ against the adelic Haar measure satisfies the same smoothness and continuity conditions at $w$ and $\Omega_w(x * f) = (\Omega_w x) * f$, $\bar\Omega_w(x * f) = (\bar\Omega_w x) * f$.
--
--   This packages the $\mathrm{Ad}$-invariance and centrality of the two Casimir elements of $\mathfrak{gl}_2(\mathbb{C})$ at a complex place, in the concrete form needed for functions on $\mathrm{GL}_2(\mathbb{A}_K)$: the Casimir eigenspaces are stable under right translation by the local row-isometry groups and under right convolution by bi-finite factorizable test functions. It is used in the analysis of cuspidal constituents, where these stabilities allow one to conclude that each Casimir operator acts on a cuspidal constituent by a scalar.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex.lean

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

theorem AutomorphicForm.archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    (∀ (w' : InfinitePlace K) (k : rowIsometrySubgroup₀ w'.Completion),
        IsArchSmoothAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightTranslate K (rowIsometryInclAt₀ K w' k) x))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d'
          (rightTranslate K (rowIsometryInclAt₀ K w' k) x)))) ∧
        archCasimirAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirAtComplex hw x) ∧
        archCasimirBarAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirBarAtComplex hw x)) ∧
    (∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (tys : AutomorphicForm.ArchTypeFamily K),
        IsFactorizableTestFn K f → IsArchBiFinite K tys f →
        IsArchSmoothAtComplex hw (rightConv K x f) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightConv K x f))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (rightConv K x f)))) ∧
        archCasimirAtComplex hw (rightConv K x f) = rightConv K (archCasimirAtComplex hw x) f ∧
        archCasimirBarAtComplex hw (rightConv K x f) = rightConv K (archCasimirBarAtComplex hw x) f) := by sorry
