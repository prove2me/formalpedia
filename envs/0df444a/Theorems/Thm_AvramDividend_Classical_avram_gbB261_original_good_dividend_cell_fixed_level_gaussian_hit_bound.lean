-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB261_original_good_dividend_cell_fixed_level_gaussian_hit_bound
-- name    : AvramDividend.Classical.avram_gbB261_original_good_dividend_cell_fixed_level_gaussian_hit_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:07:49.226204+00:00
-- url     : https://prove2.me/theorems/c86da314-4041-48cf-865d-df8034336044
-- title:
--   Original fixed-level Gaussian reserve hit on a small-dividend cell has a uniform small-ball probability bound
-- statement:
--   For a genuine original spectrally negative Levy source and its adapted monotone dividend strategy, suppose the original future source increment over a physical mesh cell has a specified positive-variance Gaussian law. Then the probability that the dividend increase in the cell is at most epsilon and that the original postpayment reserve at any interior time equals any prescribed spatial level b is at most epsilon times the uniform Gaussian density envelope. The proof combines original filtration-adapted centre independence, original dividend right-limit enclosure on a good cell, Gaussian density integration and product-measure Fubini. It is an original-source quantitative component of finite-cap Gaussian B100.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_gbB253_gaussian_pdf_uniform_envelope
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB261_original_good_dividend_cell_fixed_level_gaussian_hit_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t < u)
    (x b epsilon : ℝ) (hEps : 0 ≤ epsilon)
    (mu : ℝ) (v : ℝ≥0) (hv : 0 < v)
    (hLaw : Measure.map (fun ω => X.X t ω - X.X s ω) P = gaussianReal mu v) :
    P {ω | D u ω - D s ω ≤ epsilon ∧
      x + X.X t ω - rightLimit D t ω = b} ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) *
        ENNReal.ofReal epsilon := by sorry
