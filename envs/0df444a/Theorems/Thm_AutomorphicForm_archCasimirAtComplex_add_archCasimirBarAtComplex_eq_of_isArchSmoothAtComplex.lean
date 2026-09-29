-- Prove2me | Theorems.Thm_AutomorphicForm_archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex
-- name    : AutomorphicForm.archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/d350480a-76d4-52d3-8972-c97372255816
-- title:
--   Sum of the two Casimir operators at a complex place
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$ with `w.IsComplex`, and $\varphi\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ a function on the adelic group `AdelicGL2 (𝓞 F) F`, i.e. on $\mathrm{GL}_2$ of the adele ring of $F$. Assume `IsArchSmoothAtComplex hw φ`: for every $g$ the function $e\mapsto \varphi(g\cdot\mathrm{archComplexLiftAt}_{hw}(e))$ on $2\times 2$ complex matrices is $C^\infty$ (in the real sense) on the locus of invertible $e$, where `archComplexLiftAt` sends an invertible $e$ to its image in $\mathrm{GL}_2(\mathbb{A}_F)$ at the place $w$. Write $D_d\varphi(g)=\frac{d}{dt}\varphi(g\cdot\mathrm{archFlowAtComplex}_{hw}(d,t))|_{t=0}$ for the flow derivative along one of the six directions $d\in\{H,E,F^-,iH,iE,iF^-\}$ of `ArchDirComplex`, and for $d$ among the three `ArchDir` directions put $\partial_d=\frac12(D_{d^{\mathbb C}}-i\,D_{d^{i}})$ and $\bar\partial_d=\frac12(D_{d^{\mathbb C}}+i\,D_{d^{i}})$, where $d^{\mathbb C}=$`d.toComplex` and $d^{i}=$`d.toComplexI` are the associated real and imaginary complex directions. With $\Omega\varphi=-(\frac14\partial_H\partial_H\varphi-\frac12\partial_H\varphi+\partial_E\partial_{F^-}\varphi)$ and $\bar\Omega\varphi$ its barred analogue, and with the compact operator $\Omega_K\varphi=D_{iH}D_{iH}\varphi+\bigl(D_E(D_E\varphi-D_{F^-}\varphi)-D_{F^-}(D_E\varphi-D_{F^-}\varphi)\bigr)+\bigl(D_{iE}(D_{iE}\varphi+D_{iF^-}\varphi)+D_{iF^-}(D_{iE}\varphi+D_{iF^-}\varphi)\bigr)$, the conclusion is the identity of functions $$\Omega\varphi+\bar\Omega\varphi=\tfrac18\Omega_K\varphi-\tfrac18\Bigl(D_HD_H\varphi+\bigl(D_E+D_{F^-}\bigr)\bigl(D_E\varphi+D_{F^-}\varphi\bigr)+\bigl(D_{iF^-}-D_{iE}\bigr)\bigl(D_{iF^-}\varphi-D_{iE}\varphi\bigr)\Bigr),$$ the last two bracketed terms being written in Lean as the indicated sums and differences of iterated flow derivatives.
--
--   This is the Cartan-type decomposition of the Casimir element at a complex place: the sum of the holomorphic and antiholomorphic Casimir operators equals one eighth of the sum of squares along the three compact directions minus one eighth of the sum of squares along the three non-compact directions. It is used in bounding the real part of the Casimir eigenvalue of a cuspidal constituent with given highest weight at a complex place, and in the $L^p$ estimates for iterated archimedean flow derivatives on Casimir eigenfunctions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) :
    archCasimirAtComplex hw φ + archCasimirBarAtComplex hw φ
      = (1 / 8 : ℂ) • archKCasimirAtComplex hw φ
        - (1 / 8 : ℂ) • (archDerivAtComplex hw .H (archDerivAtComplex hw .H φ) +
            (archDerivAtComplex hw .E (archDerivAtComplex hw .E φ + archDerivAtComplex hw .Fm φ) +
              archDerivAtComplex hw .Fm (archDerivAtComplex hw .E φ + archDerivAtComplex hw .Fm φ)) +
            (archDerivAtComplex hw .iFm (archDerivAtComplex hw .iFm φ - archDerivAtComplex hw .iE φ) -
              archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ - archDerivAtComplex hw .iE φ))) := by sorry
