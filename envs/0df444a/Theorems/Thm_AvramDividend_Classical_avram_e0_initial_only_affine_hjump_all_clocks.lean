-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_affine_hjump_all_clocks
-- name    : AvramDividend.Classical.avram_e0_initial_only_affine_hjump_all_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:15:05.675849+00:00
-- url     : https://prove2.me/theorems/1328989a-9890-4687-830c-9dfe6a19130c
-- title:
--   An affordable initial-only dividend satisfies the original affine HJB jump condition at every clock
-- statement:
--   For a verification candidate which agrees with one plus the reserve on nonnegative capital, an initial nonnegative dividend payment bounded by initial capital satisfies the exact Avram jump loss inequality for every sample and time. At zero the loss equals the payment, while at all later clocks the dividend has no jump.
-- source:
--   Original Avram hjump hypothesis e0b94d7f, accepted rightLimit 7fa270ec.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_rightlimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_initial_only_affine_hjump_all_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ)
    (hKnonneg : ∀ ω, 0 ≤ K ω)
    (hKle : ∀ ω, K ω ≤ x)
    (w : ℝ → ℝ) (hw_affine : ∀ y, 0 ≤ y → w y = 1 + y) :
    ∀ ω (t : ℝ≥0),
      rightLimit (fun s ω => if s = 0 then 0 else K ω) t ω -
          (if t = 0 then 0 else K ω) ≤
        w (riskProcess X x (fun s ω => if s = 0 then 0 else K ω) t ω) -
          w (riskProcess X x (fun s ω => if s = 0 then 0 else K ω) t ω -
            (rightLimit (fun s ω => if s = 0 then 0 else K ω) t ω -
              (if t = 0 then 0 else K ω))) := by sorry
