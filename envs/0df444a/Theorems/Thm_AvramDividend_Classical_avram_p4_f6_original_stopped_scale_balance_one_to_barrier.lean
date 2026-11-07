-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_stopped_scale_balance_one_to_barrier
-- name    : AvramDividend.Classical.avram_p4_f6_original_stopped_scale_balance_one_to_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:35:01.424145+00:00
-- url     : https://prove2.me/theorems/0fd96441-3df0-4546-8b3a-41ccd2d30ac1
-- title:
--   Original Lévy killed stopped q-scale balance from reserve one to an upper barrier
-- statement:
--   For the actual standing spectrally negative Lévy process, the stopped q-scale value at reserve one equals its upper barrier payoff weighted by strict discounted upper-before-ruin exit expectation. Requires genuine stopped scale-function q-harmonicity, localisation and boundary accounting. The previously Proved conditional exit-ratio theorem supplies algebraic normalisation.
-- source:
--   Exact independent stochastic stopped-scale balance for original process. Proved chat04_exit_ratio_of_stopped_balance converts it to a q-scale ratio and Proved chat04_twoSidedExitExpectation_eq_corrected converts to corrected strict exits; this child is a genuine non-circular remaining source task.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_original_stopped_scale_balance_one_to_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ b : ℝ, 1 ≤ b →
      twoSidedExitExpectation X q b 1 * ENNReal.ofReal (W b) =
        ENNReal.ofReal (W 1) := by sorry
