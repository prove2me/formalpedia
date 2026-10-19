-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_lemma_22
-- name    : DriftVarCtrl.FixedLB.lemma_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:09.062674+00:00
-- url     : https://prove2.me/theorems/dbf937e0-02d7-4deb-b1a2-4f9a58f41fdf
-- title:
--   Lemma 22, p. EC-32 — under (9): Mμ₂ + h₂U > 0 and h₂μ₁ − μ₂h₁ < 0
-- statement:
--   Assume $v_1 < v_2$ and $h_1 > h_1^*$ (that is, $\Delta h_1 > 0$), and let
--   $$h_2 \in \big(d_2^L\Delta h_1 + h_2^*,\ d_1^U\Delta h_1 + h_2^*\big).$$
--   Then
--   $$M\mu_2 + h_2U > 0,\qquad h_2\mu_1 - \mu_2h_1 < 0 .$$
--
--   These sign facts are used in Lemmas 6 and 9 to control the shape of the two-interval value in region (9).
--
--   **Formalization Note.** Here $h_2$ is a free real argument (as in Lemmas 4–10) and $h_1$ is the model's control-1 cost. The page prints (204) as $h_2\mu_1 - \mu_2h_1 \le 0$; its proof establishes the strict inequality and Lemma 9's proof uses it, so the strict form is stated. The standing $v_1 < v_2$ (p. 12) is the hypothesis `hv`.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-32, Appendix D, Lemma 22, (203)–(204)

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants

namespace DriftVarCtrl.FixedLB

/-- Lemma 22 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-32, (203)–(204)). Let `h₁ > h*₁` and
`h₂ ∈ (dᴸ₂Δh₁ + h*₂, dᵁ₁Δh₁ + h*₂)`. Then `Mμ₂ + h₂U > 0` and `h₂μ₁ − μ₂h₁ < 0`.

Formalization Note: the control-2 cost is the free argument `h₂'` (as in Lemmas 4–10), `h₁ = p.h₁`.
(204) is printed with `≤ 0`; its proof shows `< 0` and Lemma 9's proof uses the strict form, so the
strict form is stated. The standing `v₁ < v₂` (p. 12) is the hypothesis `hv`. -/
theorem lemma_22 (p : Params) (hv : v p .one < v p .two) (h1 : 0 < Δh p .one) (h₂' : ℝ)
    (h₂mem : h₂' ∈ Set.Ioo (dL2 p * Δh p .one + hstar p .two) (dU1 p * Δh p .one + hstar p .two)) :
    0 < p.M * p.μ₂ + h₂' * p.U ∧ h₂' * p.μ₁ - p.μ₂ * p.h₁ < 0 := by sorry

end DriftVarCtrl.FixedLB
