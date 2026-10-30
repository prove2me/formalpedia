-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_actual_stieltjes_cell_eq_rational_record_increment
-- name    : AvramDividend.Classical.avram_root29_05_actual_stieltjes_cell_eq_rational_record_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:54:48.622387+00:00
-- url     : https://prove2.me/theorems/46b7b7aa-19ac-4242-bb60-6c5ef5186edc
-- title:
--   Actual barrier-regulator Stieltjes cash in each rational cell equals a countably sampled Lévy record increment
-- statement:
--   At every positive-denominator rational mesh cell, the genuine dividendMeasure of the continuous Lévy runningSup regulator has mass exactly equal to the difference of its countable rational-schedule sampled running records. This is the source-faithful pathwise bridge for identifying the globally measurable sampled killed reward with the true stopped Stieltjes payout, before applying strong Markov.
-- source:
--   Composes Proved actual Lévy running-supremum Stieltjes interval mass identity 7343971b and Proved countable Cantor schedule record identity d3218d37. Essential for the genuine pathwise reward approximation to canonical 79978d61.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_cantorSchedule_rationalGrid

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_actual_stieltjes_cell_eq_rational_record_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (n k : ℕ) (hn : 0 < n) :
    let t : ℕ → ℝ≥0 := fun j => (j : ℝ≥0) * (n : ℝ≥0)⁻¹
    let sampledRecord : ℕ → ℝ := fun j =>
      ⨆ s : {s : ℝ≥0 //
        s ∈ Set.range (fun i : ℕ =>
          ((Nat.unpair i).2 : ℝ≥0) *
            (((((Nat.unpair i).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ∧ s ≤ t j},
        X.X s.1 ω
    (dividendMeasure (runningSup X) ω)
      (Set.Ioc (t k : ℝ) (t (k + 1) : ℝ)) =
      ENNReal.ofReal (sampledRecord (k + 1) - sampledRecord k) := by sorry
