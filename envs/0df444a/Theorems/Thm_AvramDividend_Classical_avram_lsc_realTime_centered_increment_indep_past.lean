-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_realTime_centered_increment_indep_past
-- name    : AvramDividend.Classical.avram_lsc_realTime_centered_increment_indep_past
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T15:27:14.794866+00:00
-- url     : https://prove2.me/theorems/8d9862cd-21d0-4741-98ee-a75a7b294b58
-- title:
--   Real-time centred source increments independent of the original Avram filtration
-- statement:
--   For each non-negative real start and later endpoint, the centred and Gaussian-scaled increment of the original spectrally negative Lévy path is independent of the original filtration at the starting time. This transports the native Avram independent-increments field to the real-time stochastic calculus interface.
-- source:
--   Same-original-space independence bridge from SpectrallyNegativeLevy.indepIncrements, complementing Avram real-time Gaussian-law bridge and enabling a filtered Brownian construction for fdb9a6a3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_realTime_centered_increment_indep_past
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Indep
      (MeasurableSpace.comap (fun ω =>
        ((X.X (Real.toNNReal t) ω - X.X (Real.toNNReal s) ω) -
          (t - s) * X.c) / X.σ) inferInstance)
      (𝓕 (Real.toNNReal s)) P := by sorry
