-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_real_payment_stieltjes_zero_cap_spatial_eventual_cover
-- name    : AvramDividend.Classical.avram_wave7_19_original_real_payment_stieltjes_zero_cap_spatial_eventual_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:24:42.058924+00:00
-- url     : https://prove2.me/theorems/8670c341-1c19-4483-a9ee-38debd49e9a4
-- title:
--   Actual original real Stieltjes ruin-payment times are eventually covered by zero/cap boundary and shrinking postpayment interior bands
-- statement:
--   The exact real-domain paymentTimes intersected with a finite horizon (including t=0 and excluding the positive ruin endpoint) are eventually included in the union of zero- and cap-reserve state boundaries and genuine interior state bands, for any lower cutoffs tending to zero and upper cutoffs tending to C. The reserve is evaluated at the source real time's toNNReal physical clock after the right-dividend atom. Uses only existing original admissibility/solvency and casts, with no continuity at ruin, no occupation-time deletion of singular cap dividends and no new canonical assumptions. This is the pointwise hypothesis needed to instantiate the already accepted W7-19 source nonnested joint-support Fatou expected cash bridge.
-- source:
--   Original paymentTimes and ruinTime, the already Proved original capped after-payment reserve bounds, and filter eventuality for spatial lower/upper cutoffs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_within_cap_before_ruin
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_real_payment_stieltjes_zero_cap_spatial_eventual_cover
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C) (T : ℝ)
    (lower : ℕ → ℝ) (upper : ℕ → ℝ≥0∞)
    (hlower : Filter.Tendsto lower Filter.atTop (𝓝 0))
    (hupper : Filter.Tendsto upper Filter.atTop (𝓝 C)) :
    ∀ (ω : Ω) (t : ℝ),
      t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T →
      ∀ᶠ n : ℕ in Filter.atTop,
        x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω = 0 ∨
          ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) = C ∨
            (lower n < x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω ∧
              ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) < upper n) := by sorry
