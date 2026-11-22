-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_nnreal_stopping_to_real_clock
-- name    : AvramDividend.Classical.avram_lsc_nnreal_stopping_to_real_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T16:05:22.270262+00:00
-- url     : https://prove2.me/theorems/4360d638-81b9-4237-963a-21cabe7d3dd0
-- title:
--   Carry any original Avram nonnegative stopping time into the real-time filtered Brownian clock
-- statement:
--   Let the real-indexed filtration be exactly the original Avram right-continuous filtration composed with Real.toNNReal. Every finite nonnegative-time stopping clock with respect to the original filtration is then a real-time stopping clock with respect to this real-indexed filtration after coercion from nonnegative to real time. The proof handles t less than zero as an empty event and nonnegative t as an identical stopped event. This is required to use LevyStochCalc's imported stopped Brownian stochastic integral with Avram's ruin-clipped stopping clock.
-- source:
--   Original Avram P4-F stopped Ito component bridge, connecting the exact stopping-time hypothesis of fdb9a6a3 to LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_eq_of_le_readable, with same-space filtered Brownian interface 2a260b0b-caa5-43ac-8917-ff05bcc10f8e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_nnreal_stopping_to_real_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} (ℱr : Filtration ℝ mΩ)
    (hℱr : ∀ t : ℝ, ℱr t = 𝓕.rightCont (Real.toNNReal t))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    IsStoppingTime ℱr (fun ω => ((τ ω : ℝ) : WithTop ℝ)) := by sorry
