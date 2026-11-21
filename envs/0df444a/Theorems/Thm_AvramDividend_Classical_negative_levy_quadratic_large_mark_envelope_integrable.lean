-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_levy_quadratic_large_mark_envelope_integrable
-- name    : AvramDividend.Classical.negative_levy_quadratic_large_mark_envelope_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T21:25:31.190783+00:00
-- url     : https://prove2.me/theorems/a2cbd79a-0cdf-409c-a4ab-327afd87ad0d
-- title:
--   Original quadratic and large-negative-mark envelope is integrable
-- statement:
--   The Lévy quadratic condition ensures min(1,y²) is integrable; a separate large-mark signed first moment makes the indicator-weighted absolute value integrable. Their weighted sum is an integrable envelope for compensated small jumps and uncompensated large jumps, without bounded variation.
-- source:
--   Pinned Mathlib lintegral_ofReal_ne_top_iff_integrable and integrable_indicator_iff, original source bridge 847641c4.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.negative_levy_quadratic_large_mark_envelope_integrable
    (ν : Measure ℝ)
    (hQuad : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤)
    (hLarge : IntegrableOn (fun y : ℝ => y) (Iic (-1 : ℝ)) ν)
    (θ : ℝ) :
    Integrable (fun y : ℝ =>
      θ / 2 * min 1 (y ^ 2) +
        |(Iic (-1 : ℝ)).indicator (fun z : ℝ => z) y|) ν := by sorry
