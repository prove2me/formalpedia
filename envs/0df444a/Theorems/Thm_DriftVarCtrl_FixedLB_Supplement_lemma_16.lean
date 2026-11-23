-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_Supplement_lemma_16
-- name    : DriftVarCtrl.FixedLB.Supplement.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:38:54.364443+00:00
-- url     : https://prove2.me/theorems/c574413e-4b79-4122-83d9-46d0e7304f7e
-- title:
--   Lemma 16, p. EC-28 — when h⁺₁(Ũ) = h₁, the point (h⁺₁(Ũ), hᵀ₂(Ũ)) lies on the upper curve (28)
-- statement:
--   For an upper boundary $\tilde U>0$ write $h^+_1(\tilde U)$, $d^U_1(\tilde U)$, $h^*_i(\tilde U)$ for the quantities (17), (12), (4) of the model with upper boundary $\tilde U$. If $\tilde U$ satisfies $h^+_1(\tilde U)=h_1$, then
--   $$d^U_1(\tilde U)\bigl(h_1-h^*_1(\tilde U)\bigr)+h^*_2(\tilde U)=\frac{\mu_2}{\mu_1}h_1\Bigl[1+\frac{v_2-v_1}{v_2}LW\bigl(-e^{-1-\frac{(-M)\mu_1v_1}{h_1}}\bigr)\Bigr]. \tag{175}$$
--   In other words the threshold $h^T_2(\tilde U)$ of (20) for the boundary $\tilde U$ equals the upper curve $\hat h_2(h_1)$, so the point $(h^+_1(\tilde U),h^T_2(\tilde U))$ lies on the upper curve (28).
--
--   The proof of Theorem 3 (c) uses this to place the box of (23) inside region (27).
--
--   **Formalization Note** The $\tilde U$-quantities are those of `withU p Ũ hŨ`. The standing $v_1<v_2$ of p. 12 is a hypothesis.
--
--   Differences from the source:
--
--   - encoding: h⁺ᵢ(Ũ), dᴸ₂(Ũ), dᵁ₁(Ũ), h*ᵢ(Ũ): the quantities (4), (13), (12), (17) with U replaced by Ũ → the same definitions evaluated at withU p Ũ hŨ (the parameters of p with upper boundary Ũ); reason: same formulas; only the upper boundary changes
--   - encoding: LW is the Lambert W function on [−1/e, ∞) → LiquidWelfareFPA.lambertW, the principal branch (the unique y ≥ −1 with ye^y = x), with the value 0 below −1/e; reason: the argument −e^{−1−(−M)μ₁v₁/h₁} lies in (−1/e, 0) for h₁ > 0, so the junk value is never evaluated
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-28, Lemma 16, (175)–(179)

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_FreeModel
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

namespace DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Lemma 16 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-28, (175)). When `Ũ > 0` satisfies `h⁺₁(Ũ) = h₁`,
`dᵁ₁(Ũ)(h₁ − h*₁(Ũ)) + h*₂(Ũ) = (μ₂/μ₁) h₁ [1 + ((v₂ − v₁)/v₂) LW(−e^{−1−(−M)μ₁v₁/h₁})]`;
in other words `hᵀ₂(Ũ)` (the threshold (20) of the model with upper boundary `Ũ`) equals the
upper curve (28) at `h₁`.

Formalization Note: `dᵁ₁(Ũ)`, `h*ᵢ(Ũ)`, `hᵀ₂(Ũ)` are those of `withU p Ũ hŨ` (same drifts,
volatilities, costs and `M`, upper boundary `Ũ`). The standing `v₁ < v₂` (p. 12) is `hv`. -/
theorem lemma_16 (p : Params) (hv : v p .one < v p .two) (Ũ : ℝ) (hŨ : 0 < Ũ)
    (hplus_eq : hplusU p .one Ũ = p.h₁) :
    dU1 (withU p Ũ hŨ) * (p.h₁ - hstar (withU p Ũ hŨ) .one) + hstar (withU p Ũ hŨ) .two
        = upperCurve p p.h₁ ∧
      hT2 (withU p Ũ hŨ) = upperCurve p p.h₁ := by sorry

end DriftVarCtrl.FixedLB.Supplement
