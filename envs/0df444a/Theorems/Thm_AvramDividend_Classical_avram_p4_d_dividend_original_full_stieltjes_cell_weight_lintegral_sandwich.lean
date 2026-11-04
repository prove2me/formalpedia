-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_cell_weight_lintegral_sandwich
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_cell_weight_lintegral_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:32:14.171885+00:00
-- url     : https://prove2.me/theorems/beb92242-06ec-437d-8cb7-a2e264267b9f
-- title:
--   Exact original Stieltjes cell integral bounded by full measure mass times lower and upper weights
-- statement:
--   For the actual Stieltjes measure of an original dividend strategy, prove a lower and upper bound for a closed-right payment cell's lintegral when the weight is pointwise bounded on that interval. This handles all of the original measure, including singular-continuous mass and the terminal right atom, without density hypotheses. In tandem with the exponential discount sandwich it enables a rigorous within-cell discount estimate for mesh convergence.
-- source:
--   Original dividendMeasure D; avram source discounted Cash, Proposition 4(i) (5.10)-(5.12); Mathlib lintegral_mono_ae and ae_restrict_mem

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_cell_weight_lintegral_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (lo hi : ℝ≥0∞) (f : ℝ → ℝ≥0∞)
    (hlo : ∀ u ∈ Ioc (a : ℝ) (b : ℝ), lo ≤ f u)
    (hhi : ∀ u ∈ Ioc (a : ℝ) (b : ℝ), f u ≤ hi) :
    lo * dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≤
      (∫⁻ u in Ioc (a : ℝ) (b : ℝ), f u ∂(dividendMeasure D ω)) ∧
    (∫⁻ u in Ioc (a : ℝ) (b : ℝ), f u ∂(dividendMeasure D ω)) ≤
      hi * dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := by sorry
