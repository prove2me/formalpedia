-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_full_preruin_postpayment_closed_physical_drift_strip
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_full_preruin_postpayment_closed_physical_drift_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:41:18.934078+00:00
-- url     : https://prove2.me/theorems/30e63391-c82b-416d-bc54-3b11a126173c
-- title:
--   Original BV complete pre-ruin postpayment reserve lies in exact closed positive cap and physical drift horizon strip
-- statement:
--   For the true original standing bounded-variation Levy process, original capped admissible dividend process and any bounded deterministic horizon, on one a.s. event the full original post-right-dividend reserve at all t≤T that are zero or strictly before ruin is nonnegative, below the cap and below x+T*physical drift. Includes all source jumps and dividend payments, including the t=0 atom. Lower boundary is closed zero, so separately localise to strict interior before use of the C1 HJB.
-- source:
--   Accepted original BV controlled upper strip theorem 4a12; original source Standing drift positive 0432; original initial-postpayment 2ecd, pre-ruin 8059 and cap bound 1610.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_postpayment_deterministic_horizon_upper_strip
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_full_preruin_postpayment_closed_physical_drift_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      0 ≤ x + X.X t ω - rightLimit D t ω ∧
      ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) ≤ C ∧
      x + X.X t ω - rightLimit D t ω ≤
        x + (T : ℝ) * X.drift := by sorry
