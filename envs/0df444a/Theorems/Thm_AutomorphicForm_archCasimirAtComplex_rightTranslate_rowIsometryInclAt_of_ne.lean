-- Prove2me | Theorems.Thm_AutomorphicForm_archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne
-- name    : AutomorphicForm.archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/678aa3bc-8eec-57aa-84e3-104ae7c12f61
-- title:
--   Complex-place Casimir operators commute with translation at other places
-- statement:
--   Let $K$ be a number field, $w$ an infinite place of $K$ with $w$ complex, and $x\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ a function on the adelic group $\mathrm{GL}_2$ of $K$. Assume $x$ is continuous; that $x$ is smooth at $w$ in the sense of `IsArchSmoothAtComplex`, i.e. for every $g$ the map sending a $2\times 2$ complex matrix $e$ to $x(g\cdot \iota_w(e))$, where $\iota_w$ places $e$ in the component at $w$ when $\det e \neq 0$, is $C^\infty$ over $\mathbb{R}$ on $\{e : \det e \neq 0\}$; and that for each of the six directions $d \in \{H,E,F^-,iH,iE,iF^-\}$ the derivative $D_d x$, given by $g \mapsto \frac{d}{dt}x(g\cdot \iota_w(\exp\text{-type flow at }t))|_{t=0}$, is continuous, as is each second derivative $D_d D_{d'} x$. Then for every infinite place $w' \neq w$ and every $k$ in the subgroup `rowIsometrySubgroup₀` of $\mathrm{GL}_2(K_{w'})$, with image $\tilde k$ under the place-$w'$ inclusion `rowIsometryInclAt₀`, the right translate $R_{\tilde k}x = (g \mapsto x(g\tilde k))$ is again smooth at $w$, has continuous first and second derivatives $D_d$, $D_dD_{d'}$, and satisfies $\Omega_w(R_{\tilde k}x) = R_{\tilde k}(\Omega_w x)$ and $\bar\Omega_w(R_{\tilde k}x) = R_{\tilde k}(\bar\Omega_w x)$, where $\Omega_w\varphi = -\left(\tfrac14\partial_H\partial_H\varphi - \tfrac12\partial_H\varphi + \partial_E\partial_{F^-}\varphi\right)$ with $\partial_d = \tfrac12(D_d - iD_{id})$, and $\bar\Omega_w$ is the same expression in $\bar\partial_d = \tfrac12(D_d + iD_{id})$.
--
--   This is the complex-place form of the statement that the holomorphic and antiholomorphic Casimir operators attached to a complex place $w$, together with the regularity conditions they presuppose, are unaffected by right translation by elements placed at another infinite place. It is used in the construction of cuspidal constituents, where the joint eigenspaces of the pair $(\Omega_w,\bar\Omega_w)$ must be shown stable under the archimedean maximal compact at the remaining places, and feeds the statements about Casimir-type test functions and right convolution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne.lean

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

theorem AutomorphicForm.archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    ∀ (w' : InfinitePlace K) (hw' : w' ≠ w) (k : rowIsometrySubgroup₀ w'.Completion),
        IsArchSmoothAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightTranslate K (rowIsometryInclAt₀ K w' k) x))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d'
          (rightTranslate K (rowIsometryInclAt₀ K w' k) x)))) ∧
        archCasimirAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirAtComplex hw x) ∧
        archCasimirBarAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirBarAtComplex hw x) := by sorry
