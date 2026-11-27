-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_Supplement_lemma_17
-- name    : DriftVarCtrl.FixedLB.Supplement.lemma_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:40:37.1517+00:00
-- url     : https://prove2.me/theorems/ffe91055-6bb1-47af-a360-10c890f56ae0
-- title:
--   Lemma 17, pp. EC-28–EC-29 — when h⁺₂(Ũ) = h₂, the point (hᵀ₁(Ũ), h⁺₂(Ũ)) lies on the lower curve (29)
-- statement:
--   For an upper boundary $\tilde U>0$ write $h^+_2(\tilde U)$, $d^L_2(\tilde U)$, $h^*_i(\tilde U)$ for the quantities (17), (13), (4) of the model with upper boundary $\tilde U$. If $\tilde U$ satisfies $h^+_2(\tilde U)=h_2$, then
--   $$\frac{1}{d^L_2(\tilde U)}\bigl(h_2-h^*_2(\tilde U)\bigr)+h^*_1(\tilde U)=\frac{\sigma_1^2}{\sigma_2^2}h_2. \tag{180}$$
--   In other words the threshold $h^T_1(\tilde U)$ of (20) for the boundary $\tilde U$ equals $\frac{\sigma_1^2}{\sigma_2^2}h_2$, so the point $(h^T_1(\tilde U),h^+_2(\tilde U))$ lies on the lower curve (29), $h_2=\frac{\sigma_2^2}{\sigma_1^2}h_1$.
--
--   The proof of Theorem 3 (c) uses this to place the box of (23) inside region (27).
--
--   **Formalization Note** The $\tilde U$-quantities are those of `withU p Ũ hŨ`. The standing $v_1<v_2$ of p. 12 is a hypothesis.
--
--   Differences from the source:
--
--   - encoding: h⁺ᵢ(Ũ), dᴸ₂(Ũ), dᵁ₁(Ũ), h*ᵢ(Ũ): the quantities (4), (13), (12), (17) with U replaced by Ũ → the same definitions evaluated at withU p Ũ hŨ (the parameters of p with upper boundary Ũ); reason: same formulas; only the upper boundary changes
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. EC-28–EC-29, Lemma 17, (180)–(189)

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_FreeModel
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

namespace DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Lemma 17 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. EC-28–EC-29, (180)). When `Ũ > 0` satisfies `h⁺₂(Ũ) = h₂`,
`(1/dᴸ₂(Ũ))(h₂ − h*₂(Ũ)) + h*₁(Ũ) = (σ₁²/σ₂²) h₂`; in other words `(hᵀ₁(Ũ), h₂)` lies on the
lower curve (29) `h₂ = (σ₂²/σ₁²) h₁`.

Formalization Note: `dᴸ₂(Ũ)`, `h*ᵢ(Ũ)`, `hᵀ₁(Ũ)` are those of `withU p Ũ hŨ` (upper boundary
`Ũ`). The standing `v₁ < v₂` (p. 12) is `hv`. -/
theorem lemma_17 (p : Params) (hv : v p .one < v p .two) (Ũ : ℝ) (hŨ : 0 < Ũ)
    (hplus_eq : hplusU p .two Ũ = p.h₂) :
    1 / dL2 (withU p Ũ hŨ) * (p.h₂ - hstar (withU p Ũ hŨ) .two) + hstar (withU p Ũ hŨ) .one
        = p.σ₁ ^ 2 / p.σ₂ ^ 2 * p.h₂ ∧
      hT1 (withU p Ũ hŨ) = p.σ₁ ^ 2 / p.σ₂ ^ 2 * p.h₂ := by sorry

end DriftVarCtrl.FixedLB.Supplement
