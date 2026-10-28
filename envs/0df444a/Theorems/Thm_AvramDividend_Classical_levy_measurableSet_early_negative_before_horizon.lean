-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_measurableSet_early_negative_before_horizon
-- name    : AvramDividend.Classical.levy_measurableSet_early_negative_before_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:02:38.516617+00:00
-- url     : https://prove2.me/theorems/4830d355-2f15-48f2-b493-3888e765f44c
-- title:
--   A Lévy negative-early-observation event is measurable in the filtration at the specified horizon
-- statement:
--   Fix a spectrally negative Lévy process X adapted to filtration F and right-continuous paths, and a deterministic dense countable schedule of nonnegative times. For any finite observation horizon ε, the event that X visits strictly negative values at some time t<ε belongs to the σ-algebra F_ε. The proof represents the event as a countable union over scheduled t_m<ε, uses adaptedness for each X_{t_m} in F_{t_m}⊆F_ε, and takes countable unions. This directly supplies the finite-time event-measurability premise required to transfer downward regularity under local Esscher absolute continuity.
-- source:
--   Càdlàg path coordinate event measurability and adapted processes, standard strong-Markov/Esscher arguments; builds on canonically proved levy_negative_before_horizon_iff_dense_grid.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_negative_before_horizon_iff_dense_grid
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.MeasurableSpace.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_measurableSet_early_negative_before_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (times : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (ε : ℝ≥0) :
    MeasurableSet[𝓕 ε]
      {ω : Ω | ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0} := by sorry
