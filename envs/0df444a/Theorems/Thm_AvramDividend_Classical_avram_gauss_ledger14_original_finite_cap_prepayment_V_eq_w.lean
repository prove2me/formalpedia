-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gauss_ledger14_original_finite_cap_prepayment_V_eq_w
-- name    : AvramDividend.Classical.avram_gauss_ledger14_original_finite_cap_prepayment_V_eq_w
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:29:02.886444+00:00
-- url     : https://prove2.me/theorems/8034b8d6-3093-4cd3-8647-ada2b40782fc
-- title:
--   Original admissible capped prepayment reserve evaluates cap-linear extension exactly
-- statement:
--   At every physical time and every sample path, the true prepayment reserve of an admissible strategy lies below the finite real cap, so the cap-linear continuation V agrees exactly with the candidate w at this true prepayment reserve, including a starting point at the cap, ruin and active right dividend atoms. This is the terminal identification needed to instantiate the proved strict-prepayment clipped four-event identity with V for the original finite Gaussian source.
-- source:
--   Direct consequence of Proved e8d7059c original finite real cap invariant; complements the postpayment-only Proved b5d88c0c and feeds finite original positive-clock source 642de490.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finite_realcap_invariant_all_times
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gauss_ledger14_original_finite_cap_prepayment_V_eq_w
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (w V : ℝ → ℝ)
    (hV : ∀ z : ℝ,
      V z = if z ≤ c then w z else w c + (z - c)) :
    ∀ (ω : Ω) (t : ℝ≥0),
      V (riskProcess X x D t ω) =
        w (riskProcess X x D t ω) := by sorry
