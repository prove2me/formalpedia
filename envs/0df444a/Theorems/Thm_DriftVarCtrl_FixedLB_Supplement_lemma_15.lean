-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_Supplement_lemma_15
-- name    : DriftVarCtrl.FixedLB.Supplement.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:42:41.906442+00:00
-- url     : https://prove2.me/theorems/1993ccda-b14f-4184-a584-f5ad9e67218d
-- title:
--   Lemma 15, p. EC-23 — every h > 0 equals h⁺(Ũ) for a unique Ũ > 0
-- statement:
--   Fix a control with drift $\mu$ and effective drift $v=2\mu/\sigma^2$, and for $\tilde U>0$ let $h^+(\tilde U)=-\dfrac{M\mu}{\tilde U\bigl(1-\frac{1-e^{-v\tilde U}}{v\tilde U}\bigr)}$ be the threshold (17) with upper boundary $\tilde U$. For every $h>0$ there is a unique $\tilde U>0$ with
--   $$h=h^+(\tilde U).$$
--
--   The proof of Theorem 4 (a) uses it: smooth pasting at the stopping level identifies the distance $\tilde U$ from the stopping level to $U$ through $h^+_1(\tilde U)=h_1$.
--
--   **Formalization Note** The statement is for each of the two controls and every $h>0$, not only the model's cost. The standing $v_1<v_2$ of p. 12 is a hypothesis.
--
--   Differences from the source: none.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-23, Lemma 15

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

namespace DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Lemma 15 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-23). For a control `c` and every value `h > 0` there is a unique
`Ũ > 0` with `h = h⁺(Ũ)`, where `h⁺(Ũ) = −Mμ/(Ũ(1 − (1 − e^{−vŨ})/(vŨ)))` is (17) with upper
boundary `Ũ`.

Formalization Note: `h` ranges over all positive reals, not only the model's cost of `c`. The
standing `v₁ < v₂` (p. 12) is `hv`. -/
theorem lemma_15 (p : Params) (hv : v p .one < v p .two) (c : Ctrl) (h : ℝ) (hh : 0 < h) :
    ∃! Ũ : ℝ, 0 < Ũ ∧ h = hplusU p c Ũ := by sorry

end DriftVarCtrl.FixedLB.Supplement
