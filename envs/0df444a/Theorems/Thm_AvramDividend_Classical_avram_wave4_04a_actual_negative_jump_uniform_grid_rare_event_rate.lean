-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_negative_jump_uniform_grid_rare_event_rate
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_negative_jump_uniform_grid_rare_event_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T23:52:36.158002+00:00
-- url     : https://prove2.me/theorems/c7c5e30d-0135-4f04-aca8-396bd7519f1a
-- title:
--   Original finite-activity negative Lévy intensity is the fine uniform-grid Bernoulli scaling limit
-- statement:
--   For the genuine original spectrally negative Lévy source X with finite negative activity, uniform [0,T] grid cell width T/n yields n(1−exp(−T ν((−∞,0))/n)) converging to the actual total-jump intensity T ν((−∞,0)). This removes the abstract rate hypothesis from the canonically Proved intrinsic original-X Poisson count law 63f4aa92 when actual uniform grids are supplied. No compensator, auxiliary jump process, or replacement probability space is assumed.
-- source:
--   Pinned Mathlib Real.hasDerivAt_exp 0 and HasDerivAt.tendsto_slope_zero. For c=T*X.ν(Iio0).toReal, show n(1-exp(-c/n))→c from the derivative of exp at 0. Handle c=0 by simp and c≠0 by composing the slope limit with −c/n as n→∞ in punctured neighborhoods; algebraic equality after restricting to n>0. The previously Proved original count law is a future consumer, not an assumed prerequisite for the limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_actual_negative_jump_uniform_grid_rare_event_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      (n : ℝ) *
        (1 - Real.exp (-(((T : ℝ) *
          (X.ν (Iio (0 : ℝ))).toReal) / (n : ℝ)))))
      atTop (𝓝 ((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
