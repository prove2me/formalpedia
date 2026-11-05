-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_singleton_indicator_kernel_lintegral_measurable
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_singleton_indicator_kernel_lintegral_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T20:21:47.665969+00:00
-- url     : https://prove2.me/theorems/33b061f9-4568-4137-9417-de453f2b87b7
-- title:
--   True original dividend Stieltjes singleton-diagonal kernel integral measurable in sample path and payment time
-- statement:
--   For a genuine adapted dividend strategy, the s-finite original Stieltjes kernel permits measurable integration of the Borel diagonal indicator 1_{s=t} over a dividend payment time s, jointly in the sample path ω and queried real time t. This is a source-exact first ingredient towards constructing a measurable random atomic support and diffuse selector. No canonical atom-set measurability is yet claimed.
-- source:
--   Accepted source dividendMeasure_global_sfinite_kernel_exists 766b5129 and pinned Mathlib Kernel.comap, IsSFiniteKernel.comap and Measurable.lintegral_kernel_prod_left, applied to the Borel diagonal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_singleton_indicator_kernel_lintegral_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun p : Ω × ℝ =>
      ∫⁻ s : ℝ, (if s = p.2 then (1 : ℝ≥0∞) else 0) ∂(dividendMeasure D p.1)) := by sorry
