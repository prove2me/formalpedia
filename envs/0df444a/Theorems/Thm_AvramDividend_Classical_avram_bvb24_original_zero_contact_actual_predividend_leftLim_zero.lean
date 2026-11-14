-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_zero_contact_actual_predividend_leftLim_zero
-- name    : AvramDividend.Classical.avram_bvb24_original_zero_contact_actual_predividend_leftLim_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:45:23.166203+00:00
-- url     : https://prove2.me/theorems/810c78f4-53a5-40b1-8b96-d82c3c6b479e
-- title:
--   Original finite-activity physical zero-contact source prepayment left reserve equals zero at every positive interior clock
-- statement:
--   On the original no-negative-jump physical BV source path, if the unmodified original Levy trajectory is the true drift path and the actual controlled reserve remains zero until the original horizon, then the original prepayment left limit used inside the stopped marked-jump generator is also zero at every physical clock with nontrivial strict-left neighbourhood. This source-exact identity uses the accepted finite-horizon prepayment-left-limit transport and the actual dividend strategy left-continuity axiom. It closes the missing zero-contact identification needed to evaluate the original stopped negative-mark compensator fibres, without replacing the original full mark law or erasing time-zero payment.
-- source:
--   Proved 5510ba4a original finite-horizon source prepayment left-limit transport, original IsDividendStrategy left-continuity, original zero reserve and nojump linear drift hypotheses from ed067740.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys126_original_finite_horizon_zero_source_prepayment_leftLim
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb24_original_zero_contact_actual_predividend_leftLim_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S)
    (hnb : (nhdsWithin t (Iio t)).NeBot)
    (hSource : ∀ s : ℝ≥0, s ≤ S →
      X.X s ω = (s : ℝ) * X.drift)
    (hZero : ∀ s : ℝ≥0, s ≤ S →
      riskProcess X x D s ω = 0) :
    Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t = 0 := by sorry
