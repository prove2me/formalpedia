-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_original_reset_affine_jump_contact
-- name    : AvramDividend.Classical.avram_bv_tail13_original_reset_affine_jump_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:39:08.44739+00:00
-- url     : https://prove2.me/theorems/609978c2-792a-4562-9d04-8643b7c4f8f7
-- title:
--   Original reserve reset meets affine payout verification contact before ruin
-- statement:
--   For the actual original Levy process, a positive deterministic clock and a dividend step paying the clipped original reserve at that clock, the source-exact dividend-jump contact inequality holds for the affine zero-extended verification function at zero and strictly before ruin. The reset is affordable before ruin because the original risk process remains nonnegative there.
-- source:
--   Original source riskProcess_nonneg_before_ruin makes clipped reset amount equal prepayment reserve on the surviving event. Import public Proved rightLimit and affine jump contact to derive the exact generator sign/contact condition of canonical BV tail audit.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_single_step_rightLimit_eq
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail12_single_positive_clock_reset_affine_jump_contact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail13_original_reset_affine_jump_contact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (s : ℝ≥0) (hs : 0 < s)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : ∀ t ω, D t ω = if t ≤ s then 0 else
      max (x + X.X s ω) (0 : ℝ)) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        (fun y : ℝ => if y < 0 then 0 else 1 + y) (riskProcess X x D t ω) -
          (fun y : ℝ => if y < 0 then 0 else 1 + y)
            (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) := by sorry
