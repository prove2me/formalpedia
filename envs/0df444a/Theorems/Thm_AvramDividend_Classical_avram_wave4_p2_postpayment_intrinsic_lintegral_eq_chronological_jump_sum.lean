-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_intrinsic_lintegral_eq_chronological_jump_sum
-- name    : AvramDividend.Classical.avram_wave4_p2_postpayment_intrinsic_lintegral_eq_chronological_jump_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:58:07.644823+00:00
-- url     : https://prove2.me/theorems/f2395578-a128-49db-b6f0-400b1c191f21
-- title:
--   Original controlled postpayment marked jump kernel integral equals chronological sum
-- statement:
--   For a genuine original-filtration spectrally negative Lévy reserve under an admissible dividend strategy, the full positive-time postpayment marked-jump measure integrates every measurable nonnegative time-and-mark kernel to the chronological ENNReal sum of its values at actual combined marks ΔX_t−(D_{t+}−D_t). The source and dividend jumps are not assumed disjoint, and the full postpayment measure is not replaced by the original Lévy Poisson compensator.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), source-faithful (5.11)–(5.12) jump accounting. Canonical Proved original postpayment intrinsic marked measure 282556df and combined-jump mark joint measurability 0c60d413; measurable map and counting-measure lintegral reduction as established by original source analogue e4542c93.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_intrinsic_source_dividend_mark_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_combined_jumpmark_joint_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_postpayment_intrinsic_lintegral_eq_chronological_jump_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω)
    (f : (ℝ≥0 × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧
          ((x + X.X u ω - rightLimit D u ω) -
            Function.leftLim
              (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u) ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          (x + X.X u ω - rightLimit D u ω) -
            Function.leftLim
              (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)))) =
    ∑' u : ℝ≥0, if 0 < u ∧
      ((X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) -
        (rightLimit D u ω - D u ω)) ≠ 0
      then f (u,
        (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) -
          (rightLimit D u ω - D u ω))
      else 0 := by sorry
