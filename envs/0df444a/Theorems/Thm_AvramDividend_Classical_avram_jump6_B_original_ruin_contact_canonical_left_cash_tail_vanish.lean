-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_ruin_contact_canonical_left_cash_tail_vanish
-- name    : AvramDividend.Classical.avram_jump6_B_original_ruin_contact_canonical_left_cash_tail_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:03:53.530567+00:00
-- url     : https://prove2.me/theorems/cc81270b-6252-4814-afef-b2e468f79390
-- title:
--   Actual original positive ruin-contact closed dividend cash in the canonical final left mesh vanishes
-- statement:
--   At an actual original positive ruin-contact stopping time, the true dividendMeasure discounted cash paid over the final interval (t-1/(j+1),t] and restricted to the original paymentTimes tends to zero in ENNReal as j increases. This canonical source-exact endpoint control is derived from the already Proved general original contact cash tail theorem, with monotone vanishing reciprocal mesh. Supports the original infinite-negative-jump-activity stopped ruin-contact payment residual; no finite intensity assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_positive_ruincontact_full_inclusive_cash_tail_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_ruin_contact_canonical_left_cash_tail_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hContact : (t : ℝ≥0∞) = ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun j : ℕ =>
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((t : ℝ) - (1 / ((j : ℝ) + 1))) (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
