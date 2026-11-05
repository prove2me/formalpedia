-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_compact_band_true_stopped_strictpre_deriv_L1
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_compact_band_true_stopped_strictpre_deriv_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:24:15.651847+00:00
-- url     : https://prove2.me/theorems/ecbf62fd-ff48-4688-a3ca-9f8b8c3d89f8
-- title:
--   Original stopped strict-prejump dividend gradient is Stieltjes-integrable on compact interior reserve bands
-- statement:
--   The original unbounded-variation C2 HJB interior assumption supplies a uniform first-derivative bound on a compact reserve band. At the true stopped dividendMeasure, whenever the genuine left-Lévy-limit/right-dividend-limit reserve is almost surely in that band and its gradient kernel is strongly measurable, that actual gradient is pathwise Stieltjes-integrable. The theorem covers the original singular-continuous and right-atomic control mass and supplies a genuine source-specific local L1 condition for stopped Ito-Meyer control. It does not assume global derivative boundedness or ignore boundary contact.
-- source:
--   Compose Proved pinned original UBV compact derivative bound 8e186779 with Proved original true stopped dividend Stieltjes finite-measure integrability 617614f3; source state is the strict Lévy left limit and right dividend limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_compact_interior_derivative_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_bounded_signed_stieltjes_integrableOn
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_compact_band_true_stopped_strictpre_deriv_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hSM : AEStronglyMeasurable
      (fun s : ℝ => deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω))
      ((dividendMeasure D ω).restrict (paymentTimes σ ∩ Iic (T : ℝ))))
    (hstate : ∀ᵐ s ∂(dividendMeasure D ω).restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω ∈ Icc a b) :
    IntegrableOn (fun s : ℝ => deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω) := by sorry
