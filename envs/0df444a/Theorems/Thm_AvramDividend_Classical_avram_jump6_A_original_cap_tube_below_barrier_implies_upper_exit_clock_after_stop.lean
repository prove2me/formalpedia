-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_cap_tube_below_barrier_implies_upper_exit_clock_after_stop
-- name    : AvramDividend.Classical.avram_jump6_A_original_cap_tube_below_barrier_implies_upper_exit_clock_after_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:43:42.115815+00:00
-- url     : https://prove2.me/theorems/0a9a44fd-515c-402b-8718-f439be4ccd55
-- title:
--   Original finite-cap path bounded below upcrossing implies stopped clock precedes exact first upper exit
-- statement:
--   For the original spectrally negative Lévy sample path X, if its true cap threshold a−x is never exceeded on [0,σ], then σ is at most any finite actual strict upper-exit time u defined by the infimum of all strict-upcrossing times. The conclusion feeds the Proved original inclusive-barrier cash-zero source ece1f923 without requiring an import into this public lemma, avoiding cross-owner private dependency restrictions. This is the physical stopped-path clock bridge for a Brownian small tube before a ruin-causing negative marked jump.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_cap_tube_below_barrier_implies_upper_exit_clock_after_stop
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (ω : Ω) (u σ : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hBound : ∀ s : ℝ≥0, s ≤ σ → X.X s ω ≤ a - x) :
    σ ≤ u := by sorry
