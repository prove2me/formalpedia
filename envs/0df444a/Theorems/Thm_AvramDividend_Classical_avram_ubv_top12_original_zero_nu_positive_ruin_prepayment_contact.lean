-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_positive_ruin_prepayment_contact
-- name    : AvramDividend.Classical.avram_ubv_top12_original_zero_nu_positive_ruin_prepayment_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:46:55.243123+00:00
-- url     : https://prove2.me/theorems/1208dcd5-5c13-4132-8de1-df5a3545f2eb
-- title:
--   Original zero-jump positive-ruin terminal prepayment contact and exclusion of ruin cash atom
-- statement:
--   On a single full-measure event for the original zero-jump Lévy process, every strictly positive random ruin time has pre-right-payment terminal reserve equal to the left limit of the post-right-payment reserve. The literal dividend paymentTimes interval excludes the ruin endpoint, so its Ioc and Ioo restrictions coincide. This is the positive-ruin contact branch needed for infinite-cap original Gaussian stopped Itô verification.
-- source:
--   Imports public b462 path continuity through newly proved f7a20a5c all-positive-clock reserve contact, public caa7f605 pre/post reserve left-limits, and public 1ace6ce0 strict ruin endpoint payment equality. Intended exact branch of 249c532d and 6c6f8a07, avoiding circular import of their Open target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_all_positive_clock_preright_leftlim
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn12_ruin_endpoint_payment_inter_eq
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top12_original_zero_nu_positive_ruin_prepayment_contact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      (t : ℝ≥0∞) = ruinTime X x D ω →
      Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
        riskProcess X x D t ω ∧
      ∀ a : ℝ,
        paymentTimes (ruinTime X x D ω) ∩ Ioc a (t : ℝ) =
          paymentTimes (ruinTime X x D ω) ∩ Ioo a (t : ℝ) := by sorry
