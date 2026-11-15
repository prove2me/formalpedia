-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a432_discrete_Banach_martingale_Doob_Lp_maximal
-- name    : AvramDividend.Classical.avram_ga_a432_discrete_Banach_martingale_Doob_Lp_maximal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T23:57:06.653661+00:00
-- url     : https://prove2.me/theorems/80fcaaa1-d1a5-4392-afca-33bbd9c4e1d3
-- title:
--   Doob Lp maximal inequality for Banach-valued discrete martingales
-- statement:
--   For a Banach-valued discrete-time martingale, the Lp norm of the running maximum of its norm is bounded by p/(p-1) times the terminal Lp norm for every p>1.
-- source:
--   Existing accepted Prove2Me proof of LevyStochCalc.Probability.lintegral_sq_dyadicRunMax_le_readable includes the discrete Banach martingale maximal inequality as an auxiliary. Publish this as an independently reusable theorem, using Jensen and the Proved MeasureTheory.maximal_ineq_Lp_readable.

import Mathlib
import Theorems.Thm_MeasureTheory_maximal_ineq_Lp_readable
open ProbabilityTheory ENNReal Filter Set Finset MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a432_discrete_Banach_martingale_Doob_Lp_maximal
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {𝒢 : Filtration ℕ mΩ} {f : ℕ → Ω → E} {p : ℝ}
    (hf : Martingale f 𝒢 μ) (hp : 1 < p) (n : ℕ) :
    eLpNorm (fun ω => (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun k => ‖f k ω‖))
      (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (p / (p - 1)) * eLpNorm (f n) (ENNReal.ofReal p) μ := by sorry
