-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_monotone_cap_regeneration_factor_limit
-- name    : AvramDividend.Classical.avram_ws01e_b_monotone_cap_regeneration_factor_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:09:08.187984+00:00
-- url     : https://prove2.me/theorems/38df167f-f1da-4ead-bac4-06e2cc703506
-- title:
--   Exact factorisation on all finite caps persists at their monotone union
-- statement:
--   For any two measures μ,ν, increasing natural-indexed event family E_n, measurable or nonmeasurable observation event B, and fixed nonnegative extended-real multiplier c, if μ(E_n∩B)=ν(E_n)·c for every finite cap n, then exactly the same factorisation holds on the full union E_∞=∪ E_n. The proof combines continuity from below of measure for monotone sequences, finite intersection distribution over unions, and continuity from below of multiplication in ENNReal. This is an abstract normalisation-free cap removal theorem for genuine random-terminal Esscher stopped-regeneration factorisations, including zero or infinite mass cases.
-- source:
--   Pinned Mathlib Monotone.measure_iUnion, Set membership distributivity, ENNReal.iSup_mul; does not assume the Wiener–Hopf conclusion.

import Mathlib

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_monotone_cap_regeneration_factor_limit
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (E : ℕ → Set α) (hE : Monotone E)
    (B : Set α) (c : ℝ≥0∞)
    (hFactor : ∀ n : ℕ, μ (E n ∩ B) = ν (E n) * c) :
    μ ((⋃ n : ℕ, E n) ∩ B) = ν (⋃ n : ℕ, E n) * c := by sorry
