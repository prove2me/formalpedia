-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_Supplement_lemma_14
-- name    : DriftVarCtrl.FixedLB.Supplement.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:44:43.107642+00:00
-- url     : https://prove2.me/theorems/f21eaa56-33de-48da-9a58-4075c518c1c8
-- title:
--   Lemma 14, p. EC-22 — under (27), S* = −(1/v₁) ln w > 0 and M < Ṽ₁₂^{[0,S*]}(S*) < 0
-- statement:
--   Suppose $(h_1,h_2)$ satisfies (27), $\frac{\sigma_2^2}{\sigma_1^2}h_1<h_2<\hat h_2(h_1)$, with $\hat h_2$ the upper curve (28). Let $w=\frac{v_2(\mu_2h_1-h_2\mu_1)}{h_1\mu_2(v_2-v_1)}$, $S^*=-\frac1{v_1}\ln w$ and $\tilde V_{12}^{[0,S^*]}(x)=-\frac{h_1x}{\mu_1}-\frac{h_1e^{-v_1x}}{v_1\mu_1}+\frac{h_1}{v_1\mu_1}$ (172). Then
--   $$S^*>0\qquad\text{and}\qquad M<\tilde V_{12}^{[0,S^*]}(S^*)<0 .$$
--
--   In the proof of Theorem 4 (c) this places the switch from control 1 to control 2 at a positive distance above the stopping level, with a value between $M$ and $0$ there.
--
--   **Formalization Note** The standing $v_1<v_2$ of p. 12 is a hypothesis.
--
--   Differences from the source: none.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-22, Lemma 14 (proof pp. EC-22–EC-23, (137)–(142))

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

namespace DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Lemma 14 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-22). Suppose `(h₁, h₂)` satisfies (27),
`(σ₂²/σ₁²) h₁ < h₂ < ĥ₂(h₁)`. Let `S* = −(1/v₁) ln w` with
`w = v₂(μ₂h₁ − h₂μ₁)/(h₁μ₂(v₂ − v₁))`, and `Ṽ₁₂^{[0,S*]}(x) = −h₁x/μ₁ − h₁e^{−v₁x}/(v₁μ₁) + h₁/(v₁μ₁)`
(172). Then `S* > 0` and `M < Ṽ₁₂^{[0,S*]}(S*) < 0`.

Formalization Note: `S*` is `Sstar p` and `Ṽ₁₂^{[0,S*]}` is `Vtil p`. The standing `v₁ < v₂`
is `hv`. -/
theorem lemma_14 (p : Params) (hv : v p .one < v p .two) (h27 : cond27 p) :
    0 < Sstar p ∧ p.M < Vtil p (Sstar p) ∧ Vtil p (Sstar p) < 0 := by sorry

end DriftVarCtrl.FixedLB.Supplement
