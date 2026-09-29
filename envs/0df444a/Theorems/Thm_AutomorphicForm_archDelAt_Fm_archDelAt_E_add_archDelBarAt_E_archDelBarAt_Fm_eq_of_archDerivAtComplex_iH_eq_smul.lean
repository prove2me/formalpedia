-- Prove2me | Theorems.Thm_AutomorphicForm_archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul
-- name    : AutomorphicForm.archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/57f2c705-010f-578f-bbfa-d7b2d1fa13b7
-- title:
--   Symmetric 𝔭-identity at a complex place on an iH-eigenvector
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$ with $w$ complex, and let $\varphi$ be a complex-valued function on the adelic group $\mathrm{GL}_2(\mathbb{A}_{F})$ (the general linear group of $2\times 2$ matrices over the adele ring of $\mathcal{O}_F$ in $F$). Assume $\varphi$ is smooth at $w$ in the sense of `IsArchSmoothAtComplex`: for every adelic $g$, the function sending a matrix $e \in \mathbb{C}^{2\times 2}$ to $\varphi(g\cdot\mathrm{archComplexLiftAt}\,e)$ is $C^\infty$ over $\mathbb{R}$ on the open set where $\det e \neq 0$. Let $m \in \mathbb{C}$ and assume the eigenvalue relation $D_{iH}\varphi = m\varphi$, where for each of the six directions $d \in \{H,E,F^-,iH,iE,iF^-\}$ the operator $D_d\varphi$ is defined pointwise by $(D_d\varphi)(g) = \frac{d}{dt}\varphi(g\cdot\mathrm{archFlowAtComplex}\,d\,t)\big|_{t=0}$. Write $\partial_X = \tfrac12(D_X - i D_{iX})$ and $\bar\partial_X = \tfrac12(D_X + i D_{iX})$ for $X \in \{H,E,F^-\}$, and $\Omega = -\bigl(\tfrac14\partial_H\partial_H - \tfrac12\partial_H + \partial_E\partial_{F^-}\bigr)$, $\bar\Omega = -\bigl(\tfrac14\bar\partial_H\bar\partial_H - \tfrac12\bar\partial_H + \bar\partial_E\bar\partial_{F^-}\bigr)$. The conclusion is the identity of functions $$-\bigl(\partial_{F^-}\partial_E\varphi + \bar\partial_E\bar\partial_{F^-}\varphi\bigr) = \Omega\varphi + \bar\Omega\varphi + \tfrac18 D_H D_H \varphi - \Bigl(\tfrac{m^2}{8} + \tfrac{i m}{2}\Bigr)\varphi.$$
--
--   At a complex place the Lie algebra $\mathfrak{sl}_2(\mathbb{C})$ splits as $\mathfrak{su}(2) \oplus \mathfrak{p}$, and $\partial_E + \bar\partial_{F^-}$, $\partial_{F^-} + \bar\partial_E$ are the raising and lowering operators in $\mathfrak{p}$; the identity expresses the symmetric combination of their products, on a vector of infinitesimal circle weight $m$, through the two Casimir operators of the place, the square of $D_H$ and a scalar. It is used in the analysis of cuspidal constituents at complex places, in the comparison of $\bar\Omega$ with the conjugate of $\Omega$ on $\mathfrak{sl}_2$-invariants and in the lower bound for the real part of the Casimir eigenvalue on a highest-weight vector.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) (m : ℂ)
    (hm : archDerivAtComplex hw .iH φ = m • φ) :
    -(archDelAt hw .Fm (archDelAt hw .E φ) + archDelBarAt hw .E (archDelBarAt hw .Fm φ))
      = archCasimirAtComplex hw φ + archCasimirBarAtComplex hw φ
        + (1 / 8 : ℂ) • archDerivAtComplex hw .H (archDerivAtComplex hw .H φ)
        - (m ^ 2 / 8 + Complex.I * m / 2) • φ := by sorry
