-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_real_convolution_lconvolution_ofReal_bridge
-- name    : AvramDividend.Classical.nonnegative_real_convolution_lconvolution_ofReal_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:10:47.573353+00:00
-- url     : https://prove2.me/theorems/66374f83-dcc5-4f04-9ba4-725d5f320656
-- title:
--   Pointwise ENNReal lconvolution equals ofReal of nonnegative integrable real convolution
-- statement:
--   For nonnegative real kernel and density functions with an integrable real convolution at x, Mathlib additive ENNReal lconvolution is exactly ENNReal.ofReal of the ordinary real convolution integral at x. This is the source-faithful conversion required to identify geometric renewal-measure convolution powers with the already Proved real causal renewal-power sequence. It bridges Mathlib conv_withDensity_eq_lconvolution and ofReal_integral_eq_lintegral_ofReal for the BV Esscher scaled scale identification 1ca4a724.
-- source:
--   Pinned Mathlib Analysis/LConvolution.lean lconvolution_def; MeasureTheory.ofReal_integral_eq_lintegral_ofReal; ENNReal.ofReal_mul.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.LConvolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Ring
open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.nonnegative_real_convolution_lconvolution_ofReal_bridge
    (κ f : ℝ → ℝ) (x : ℝ)
    (hκ : ∀ y : ℝ, 0 ≤ κ y) (hf : ∀ y : ℝ, 0 ≤ f y)
    (hint : Integrable (fun y : ℝ => κ y * f (x - y)) volume) :
    lconvolution (fun y : ℝ => ENNReal.ofReal (κ y))
        (fun y : ℝ => ENNReal.ofReal (f y)) volume x =
      ENNReal.ofReal (∫ y : ℝ, κ y * f (x - y) ∂volume) := by sorry
