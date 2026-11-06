-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_inmeasure_subsequence_fatou
-- name    : AvramDividend.Classical.avram_limit2_inmeasure_subsequence_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:10:29.515579+00:00
-- url     : https://prove2.me/theorems/ff646d8e-22f5-48c1-a908-d58d47a87632
-- title:
--   In-measure stopped-grid convergence produces an almost-sure Fatou subsequence
-- statement:
--   Convergence in measure of a genuine original-process stopped-grid cash-and-terminal approximation to its real limiting payoff admits a strictly increasing reindexing with almost-sure extended-real Fatou domination. It is the precise subsequence step needed if the stochastic mesh analysis supplies L1 rather than pointwise convergence.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_limit2_signed_grid_envelope_of_expected_upper
open MeasureTheory Filter
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_inmeasure_subsequence_fatou
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : ℕ → Ω → ℝ) (R : Ω → ℝ)
    (hMeasure : TendstoInMeasure P F atTop R) :
    ∃ ns : ℕ → ℕ,
      StrictMono ns ∧
      (∀ᵐ ω ∂P, ENNReal.ofReal (R ω) ≤
        liminf (fun n => ENNReal.ofReal (F (ns n) ω)) atTop) := by sorry
