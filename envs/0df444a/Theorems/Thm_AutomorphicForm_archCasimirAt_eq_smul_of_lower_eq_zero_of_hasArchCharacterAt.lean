-- Prove2me | Theorems.Thm_AutomorphicForm_archCasimirAt_eq_smul_of_lower_eq_zero_of_hasArchCharacterAt
-- name    : AutomorphicForm.archCasimirAt_eq_smul_of_lower_eq_zero_of_hasArchCharacterAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/3c73fde5-111d-531e-b5b4-b250b1a62825
-- title:
--   Casimir eigenvalue tfrac k2(1-tfrac k2) for lowest-weight vectors
-- statement:
--   Let $F$ be a number field (a field with the number-field typeclass), let $w$ be an infinite place of $F$ with $w$ real, as witnessed by `hw`, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a function on the adelic general linear group `AdelicGL2 (𝓞 F) F` $= \mathrm{GL}_2$ over the adele ring of $F$. Assume: (i) `IsArchSmoothAt hw φ`, i.e. for every $g$ the function $e \mapsto \varphi(g \cdot \mathrm{archRealLiftAt}\,hw\,e)$ on real $2\times 2$ matrices is $C^\infty$ (of order $\top$) on the open set where $\det e \neq 0$; (ii) for an integer $k$, the predicate `HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ`, expressing that $\varphi$ transforms at $w$ under the row-isometry subgroup by the character `archWeightCharAt hw k`, the $k$-th power of the character `archWeightOneAt hw` transported from $\mathbb{R}$ along the isomorphism $F_w \cong \mathbb{R}$ attached to the real place $w$; (iii) the lowering condition $D_H\varphi - i(D_E\varphi + D_{F^-}\varphi) = 0$, where $D_d\varphi(g)$ is the derivative at $t=0$ of $t \mapsto \varphi(g \cdot \mathrm{archFlowAt}\,hw\,d\,t)$ along the one-parameter flow at $w$ in direction $d \in \{H, E, F^-\}$. Then $\mathrm{archCasimirAt}\,hw\,\varphi = -\bigl(\tfrac14 D_H^2\varphi - \tfrac12 D_H\varphi + D_E D_{F^-}\varphi\bigr)$ equals $\bigl(\tfrac k2\bigl(1 - \tfrac k2\bigr)\bigr)\cdot\varphi$, as functions on `AdelicGL2 (𝓞 F) F`.
--
--   This is the standard computation of the Casimir (hyperbolic Laplacian) eigenvalue of a smooth vector of $\mathrm{SO}(2)$-weight $k$ annihilated by the lowering operator: the eigenvalue $\tfrac k2(1-\tfrac k2)$ of the discrete series of lowest weight $k$, with no irreducibility or unitarity assumption imposed. It is used downstream to read off the Casimir eigenvalue of archimedean components, for instance in the results characterising occurrence in a class by the value of `archCasimirAt` and in the positivity and reality statements for Casimir eigenvalues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archCasimirAt_eq_smul_of_lower_eq_zero_of_hasArchCharacterAt.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archCasimirAt_eq_smul_of_lower_eq_zero_of_hasArchCharacterAt
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ) (k : ℤ)
    (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ)
    (hL : archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0) :
    archCasimirAt hw φ = (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) • φ := by sorry
