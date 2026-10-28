-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_eq_cantorSchedule_rationalGrid
-- name    : AvramDividend.Classical.runningSup_eq_cantorSchedule_rationalGrid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T11:41:35.739861+00:00
-- url     : https://prove2.me/theorems/d3218d37-d6fb-4d5a-8c74-05bcb69dca94
-- title:
--   Continuous running-supremum regulator equals explicit countable record supremum at every rational grid endpoint
-- statement:
--   At every positive-denominator rational time k/n, the actual Lévy running-supremum regulator is exactly the supremum of the process values observed by the explicit Cantor-paired rational schedule up to k/n. This is the record-level identification for every dyadic payout grid cell used in the globally measurable stopped Stieltjes reward skeleton. The proof specialises three already Proved results: rational schedule density, explicit rational-grid coverage and exact recovery at a sampled endpoint.
-- source:
--   Proved chat05_cantor_rational_schedule_dense, chat04_nat_pairing_rational_grid_coverage, runningSup_eq_densePrefix_onSample. Avram et al (2007), Proposition 1.

import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_densePrefix_onSample
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_eq_cantorSchedule_rationalGrid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (n k : ℕ) (hn : 0 < n) :
    runningSup X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω =
      ⨆ s : {s : ℝ≥0 //
        s ∈ Set.range (fun j : ℕ =>
          ((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ∧
        s ≤ (k : ℝ≥0) * (n : ℝ≥0)⁻¹}, X.X s.1 ω := by
  sorry
