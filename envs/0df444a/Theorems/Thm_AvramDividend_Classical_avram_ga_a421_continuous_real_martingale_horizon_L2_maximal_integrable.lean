-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a421_continuous_real_martingale_horizon_L2_maximal_integrable
-- name    : AvramDividend.Classical.avram_ga_a421_continuous_real_martingale_horizon_L2_maximal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:41:59.693113+00:00
-- url     : https://prove2.me/theorems/1c71c2bb-0231-403f-8d0c-86cd74838453
-- title:
--   Continuous real-valued L2 martingale has integrable squared finite-horizon maximum
-- statement:
--   For a continuous real-valued martingale on a probability space with square integrable terminal value, the squared running maximum over the finite time interval is dominated by a single integrable random variable. This is the continuous-time Doob L² maximal inequality plus sample-path continuity.
-- source:
--   Doob L2 maximal inequality and countable-time approximation by continuity; Mathlib MeasureTheory.maximal_ineq provides finite discrete maximal background.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a421_continuous_real_martingale_horizon_L2_maximal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M : ℝ≥0 → Ω → ℝ)
    (hMart : Martingale M 𝓕 P)
    (hCont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => M t ω))
    (T : ℝ≥0)
    (hL2 : Integrable (fun ω => (M T ω)^2) P) :
    ∃ S : Ω → ℝ, Integrable S P ∧
      (∀ᵐ ω ∂P, 0 ≤ S ω ∧
        ∀ t : ℝ≥0, t ≤ T → (M t ω)^2 ≤ S ω) := by sorry
