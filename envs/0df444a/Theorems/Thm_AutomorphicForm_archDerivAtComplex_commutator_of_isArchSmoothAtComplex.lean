-- Prove2me | Theorems.Thm_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex
-- name    : AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/55eaebf2-3820-50ab-82f5-d8f894657f39
-- title:
--   Commutation relations for the six flow derivatives at a complex place
-- statement:
--   Let $F$ be a number field, let $w$ be an infinite place of $F$ with $w$ complex (witnessed by `hw : w.IsComplex`), and let $\varphi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $F$, i.e. on `AdelicGL2 (𝓞 F) F = Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 F) F)`. Assume `IsArchSmoothAtComplex hw φ`: for every adelic matrix $g$, the function $e \mapsto \varphi(g \cdot \mathtt{archComplexLiftAt}\,hw\,e)$ on $2\times 2$ complex matrices is $C^\infty$ in the real sense on the open set where $\det e \neq 0$, where `archComplexLiftAt` sends an invertible $e$ to its image in the adelic group under the embedding at $w$ (and to $1$ otherwise). For each of the six directions $d \in \{H, E, Fm, iH, iE, iFm\}$ of `ArchDirComplex`, write $D_d\varphi(g) = \frac{d}{dt}\varphi\bigl(g \cdot \mathtt{archFlowAtComplex}\,hw\,d\,t\bigr)\big|_{t=0}$, the derivative at $t=0$ along the one-parameter family obtained by embedding the flow matrix `archFlowMatrixComplex d t` at $w$. The conclusion is the conjunction of fifteen identities of functions on the adelic group: $D_HD_E\varphi - D_ED_H\varphi = 2\,D_E\varphi$; $D_HD_{Fm}\varphi - D_{Fm}D_H\varphi = -2\,D_{Fm}\varphi$; $D_ED_{Fm}\varphi - D_{Fm}D_E\varphi = D_H\varphi$; $D_HD_{iE}\varphi - D_{iE}D_H\varphi = 2\,D_{iE}\varphi$; $D_HD_{iFm}\varphi - D_{iFm}D_H\varphi = -2\,D_{iFm}\varphi$; $D_ED_{iFm}\varphi - D_{iFm}D_E\varphi = D_{iH}\varphi$; $D_{iE}D_{Fm}\varphi - D_{Fm}D_{iE}\varphi = D_{iH}\varphi$; $D_{iH}D_E\varphi - D_ED_{iH}\varphi = 2\,D_{iE}\varphi$; $D_{iH}D_{Fm}\varphi - D_{Fm}D_{iH}\varphi = -2\,D_{iFm}\varphi$; $D_{iH}D_{iE}\varphi - D_{iE}D_{iH}\varphi = -2\,D_E\varphi$; $D_{iH}D_{iFm}\varphi - D_{iFm}D_{iH}\varphi = 2\,D_{Fm}\varphi$; $D_{iE}D_{iFm}\varphi - D_{iFm}D_{iE}\varphi = -D_H\varphi$; and the three vanishing commutators $[D_H, D_{iH}]\varphi = [D_E, D_{iE}]\varphi = [D_{Fm}, D_{iFm}]\varphi = 0$, the scalars acting by pointwise multiplication on complex-valued functions.
--
--   These are the bracket relations of $\mathfrak{sl}_2(\mathbb{C})$, regarded as a six-dimensional real Lie algebra with basis $H, E, F, iH, iE, iF$, realised by differentiation along right translations at a complex place. They are used in the construction and manipulation of the two Casimir operators at a complex place, for instance in the comparison of `archCasimirAtComplex` with its conjugate and in the commutation of the Casimir operators with right convolution by factorisable test functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) :
    archDerivAtComplex hw .H (archDerivAtComplex hw .E φ) - archDerivAtComplex hw .E (archDerivAtComplex hw .H φ) =
      (2 : ℂ) • archDerivAtComplex hw .E φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .H φ) =
      (-2 : ℂ) • archDerivAtComplex hw .Fm φ ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .E φ) =
      (1 : ℂ) • archDerivAtComplex hw .H φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .H φ) =
      (2 : ℂ) • archDerivAtComplex hw .iE φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .H φ) =
      (-2 : ℂ) • archDerivAtComplex hw .iFm φ ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .E φ) =
      (1 : ℂ) • archDerivAtComplex hw .iH φ ∧
    archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .iE φ) =
      (1 : ℂ) • archDerivAtComplex hw .iH φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .E φ) - archDerivAtComplex hw .E (archDerivAtComplex hw .iH φ) =
      (2 : ℂ) • archDerivAtComplex hw .iE φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .iH φ) =
      (-2 : ℂ) • archDerivAtComplex hw .iFm φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .iH φ) =
      (-2 : ℂ) • archDerivAtComplex hw .E φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iH φ) =
      (2 : ℂ) • archDerivAtComplex hw .Fm φ ∧
    archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE φ) =
      (-1 : ℂ) • archDerivAtComplex hw .H φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iH φ) - archDerivAtComplex hw .iH (archDerivAtComplex hw .H φ) =
      0 ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .E φ) =
      0 ∧
    archDerivAtComplex hw .Fm (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .Fm φ) =
      0 := by sorry
