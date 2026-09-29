-- Prove2me | Theorems.Thm_AutomorphicForm_archCasimirAt_eq_raising_lowering_of_isArchSmoothAt
-- name    : AutomorphicForm.archCasimirAt_eq_raising_lowering_of_isArchSmoothAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/7a7cd2df-80a8-5610-8dc8-7a24357e1ad3
-- title:
--   Casimir at a real place via raising and lowering operators
-- statement:
--   Let $F$ be a number field, let $w$ be an infinite place of $F$ with $w$ real, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a function on the adelic general linear group `AdelicGL2 (𝓞 F) F` of $2\times 2$ matrices over the adele ring. Assume `IsArchSmoothAt hw φ`, that is: for every $g$ the function $e \mapsto \varphi(g\cdot \mathrm{archRealLiftAt}\,hw\,e)$ on real $2\times 2$ matrices is $C^\infty$ on the set of $e$ with $\det e \neq 0$. For $d$ one of the three directions $H$, $E$, $F^-$, write $D_d\varphi(g) = \frac{d}{dt}\varphi(g\cdot \mathrm{archFlowAt}\,hw\,d\,t)\big|_{t=0}$ for the right-flow derivative at $w$ (`archDerivAt`), and let $\Omega\varphi = -\bigl(\tfrac14 D_H D_H\varphi - \tfrac12 D_H\varphi + D_E D_{F^-}\varphi\bigr)$ be `archCasimirAt`. Put $L\varphi = D_H\varphi - i\,(D_E\varphi + D_{F^-}\varphi)$ and $W\varphi = D_E\varphi - D_{F^-}\varphi$. Then there is an equality of functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$: $$\Omega\varphi = -\tfrac14\bigl(D_H(L\varphi) + i\,(D_E(L\varphi) + D_{F^-}(L\varphi))\bigr) - \tfrac{i}{2}\,W\varphi + \tfrac14\bigl(D_E(W\varphi) - D_{F^-}(W\varphi)\bigr),$$ i.e. $\Omega = -\tfrac14 RL - \tfrac{i}{2}W + \tfrac14 W^2$ with $R$ the raising operator $D_H + i(D_E + D_{F^-})$.
--
--   This is the standard rewriting of the Casimir element of $\mathfrak{sl}_2$, normalised so that $y^s$ has eigenvalue $s(1-s)$, in terms of the weight-raising, weight-lowering and rotation operators at a real archimedean place; it holds for all archimedean-smooth functions, with no eigenvalue or weight hypothesis. It is used to compute the Casimir eigenvalue of a vector killed by the lowering operator, in [`AutomorphicForm.archCasimirAt_eq_smul_of_lower_eq_zero_of_hasArchCharacterAt`](thm.html#AutomorphicForm.archCasimirAt_eq_smul_of_lower_eq_zero_of_hasArchCharacterAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archCasimirAt_eq_raising_lowering_of_isArchSmoothAt.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archCasimirAt_eq_raising_lowering_of_isArchSmoothAt
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ) :
    archCasimirAt hw φ =
      -(1 / 4 : ℂ) • (archDerivAt hw .H (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ))
          + Complex.I • (archDerivAt hw .E (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ))
            + archDerivAt hw .Fm (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ))))
      - (Complex.I / 2) • (archDerivAt hw .E φ - archDerivAt hw .Fm φ)
      + (1 / 4 : ℂ) • (archDerivAt hw .E (archDerivAt hw .E φ - archDerivAt hw .Fm φ)
          - archDerivAt hw .Fm (archDerivAt hw .E φ - archDerivAt hw .Fm φ)) := by sorry
