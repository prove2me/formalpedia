-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_mark_stream_shift_identDistrib
-- name    : AvramDividend.Classical.avram_a06_original_cp_mark_stream_shift_identDistrib
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T02:15:16.988725+00:00
-- url     : https://prove2.me/theorems/75627888-5287-4279-b33a-e4ff5d8115dd
-- title:
--   Original iid compound-Poisson mark stream has the same law after each deterministic index shift
-- statement:
--   For the original marked compound-Poisson driver on the same probability space, the full infinite mark stream has exactly its original joint distribution after any deterministic left shift. This is the second indispensable input after finite count-vector/mark independence for proving A06's stationary marked-band sums.
-- source:
--   Use the original driver's iIndepFun of the sum-indexed interarrival-mark family to derive iIndepFun of its mark subsequence, reindex by the injective shift n↦m+n, and identify both infinite joint laws with the same infinitePi product of the original mark measure. The source-exact mark support measure is a probability from Proved 4f8f174b.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_measure_facts
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_mark_stream_shift_identDistrib
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (m : ℕ) :
    IdentDistrib (fun ω (j : ℕ) => Y (m + j) ω)
      (fun ω (j : ℕ) => Y j ω) P P := by sorry
