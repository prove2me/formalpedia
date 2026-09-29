-- Prove2me | Theorems.Thm_AutomorphicForm_archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul
-- name    : AutomorphicForm.archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/3f8213af-3bf3-569e-8731-cebe0ed3d5c8
-- title:
--   Symmetric 𝔭-identity at a complex place, lowest-weight form
-- statement:
--   Let $F$ be a number field, $w$ a complex infinite place of $F$, and $\varphi$ a complex-valued function on the adelic group $\mathrm{GL}_2(\mathbb{A}_{F})$ (realised as `AdelicGL2 (𝓞 F) F`). Assume `IsArchSmoothAtComplex hw φ`, i.e. for every $g$ the function $e \mapsto \varphi(g\cdot \mathrm{archComplexLiftAt}\,e)$ on $2\times 2$ complex matrices is real-$C^{\infty}$ on the locus $\det e \neq 0$, where $\mathrm{archComplexLiftAt}$ sends an invertible matrix to the corresponding adelic element supported at $w$. Here $D_X\varphi(g)$ denotes `archDerivAtComplex`, the derivative at $t=0$ of $t \mapsto \varphi(g\cdot \mathrm{archFlowAtComplex}\,X\,t)$, for $X$ running over the six directions $H,E,F,iH,iE,iF$ of the complexified Lie algebra at $w$, and $\partial_X = \tfrac12(D_X - iD_{iX})$, $\bar\partial_X = \tfrac12(D_X + iD_{iX})$ for $X \in \{H,E,F\}$ are `archDelAt` and `archDelBarAt`. Let $m \in \mathbb{C}$ and assume $D_{iH}\varphi = m\varphi$. Then $$-\bigl(\partial_E\partial_F\varphi + \bar\partial_F\bar\partial_E\varphi\bigr) = \Omega\varphi + \bar\Omega\varphi + \tfrac18 D_HD_H\varphi - \bigl(\tfrac{m^2}{8} - \tfrac{im}{2}\bigr)\varphi,$$ where $\Omega\varphi = -\bigl(\tfrac14\partial_H\partial_H\varphi - \tfrac12\partial_H\varphi + \partial_E\partial_F\varphi\bigr)$ is `archCasimirAtComplex` and $\bar\Omega$ is its conjugate analogue built from the barred operators.
--
--   This is the symmetric $\mathfrak p$-type identity at a complex place in its lowest-weight ordering, expressing the operator $-(\partial_E\partial_F + \bar\partial_F\bar\partial_E)$ on a vector of infinitesimal circle weight $m$ in terms of the two Casimir operators, the square of $D_H$ and a scalar. It is used in the analysis of cuspidal constituents at a complex place, namely in the comparison of $\bar\Omega$ with the conjugate of $\Omega$ on $\mathfrak{sl}_2$-invariant vectors and in the lower bound for the real part of the Casimir eigenvalue on a highest-weight vector.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) (m : ℂ)
    (hm : archDerivAtComplex hw .iH φ = m • φ) :
    -(archDelAt hw .E (archDelAt hw .Fm φ) + archDelBarAt hw .Fm (archDelBarAt hw .E φ))
      = archCasimirAtComplex hw φ + archCasimirBarAtComplex hw φ
        + (1 / 8 : ℂ) • archDerivAtComplex hw .H (archDerivAtComplex hw .H φ)
        - (m ^ 2 / 8 - Complex.I * m / 2) • φ := by sorry
