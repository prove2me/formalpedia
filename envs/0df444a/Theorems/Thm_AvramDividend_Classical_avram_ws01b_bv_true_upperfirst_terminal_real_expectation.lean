-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_true_upperfirst_terminal_real_expectation
-- name    : AvramDividend.Classical.avram_ws01b_bv_true_upperfirst_terminal_real_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T14:25:39.885602+00:00
-- url     : https://prove2.me/theorems/3cd88d0e-26a3-4aec-b9cd-810bc32048ad
-- title:
--   Original bounded variation strict upper-first stopped terminal real expectation Wq(x)
-- statement:
--   Under the original Standing bounded-variation spectrally negative Lévy law, the actual strict upper-first discounted terminal scale-function reward has real Bochner expectation Wq(x), obtained as the dominated limit of genuine finite-horizon stopped killed rewards. The limit is genuinely Bochner integrable.
-- source:
--   Accepted true horizon balance, upper/survivor nonnegativity, Wq(a) domination, pointwise exit limit, and generic bounded real expectation transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_true_horizon_completed_survival_integral_balance
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_stopped_horizon_components_le_scale_cap
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_horizon_split_rewards_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_horizon_split_reward_tendsto_upper_terminal
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_uniform_nonnegative_bounded_integral_transfer

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_true_upperfirst_terminal_real_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (let F : Ω → ℝ := fun ω =>
      if twoSidedExitUpTime X (a-x) ω <
          twoSidedExitDownTime X (-x) ω then
        Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
          W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω)
      else 0;
    Integrable F P ∧ (∫ ω, F ω ∂P) = W x) := by sorry
