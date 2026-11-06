-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_integrable_expected_budget_to_triple_mesh
-- name    : AvramDividend.Classical.avram_sweep16_integrable_expected_budget_to_triple_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:47:51.64404+00:00
-- url     : https://prove2.me/theorems/25e2e361-2562-47a6-9dd4-6c8f1c7482c3
-- title:
--   Integrable original stopped expected reward budget yields constant-refinement centred triple mesh
-- statement:
--   At the original probability measure, any integrable real stopped payoff Y bounded in expectation by K has an exact triple-mesh witness of the strong shape demanded by the canonical original BV certificate. Use constant-in-refinement reward Y, centred martingale-slot Y minus its mean, zero HJB-slot, and integrable absolute centred envelope. This is a logical source interface, not the missing expected stopped-reward inequality; importing this helper does not by itself prove the canonical source theorem.
-- source:
--   Original bounded-variation source certificate db6a3111: isolates its precise independent expectation-budget obligation and gives a source-faithful shortcut once that budget is separately proved. No circular proof imported.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter
noncomputable section

theorem AvramDividend.Classical.avram_sweep16_integrable_expected_budget_to_triple_mesh
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (K : ℝ)
    (hYInt : Integrable Y P)
    (hBudget : (∫ ω, Y ω ∂P) ≤ K) :
    ∃ Ymesh Mmesh Bmesh : ℕ → Ω → ℝ,
      ∃ M B DM DB : Ω → ℝ,
        (∀ n, AEStronglyMeasurable (Mmesh n) P) ∧
        (∀ n, AEStronglyMeasurable (Bmesh n) P) ∧
        Integrable DM P ∧ Integrable DB P ∧
        (∀ n, ∀ᵐ ω ∂P, |Mmesh n ω| ≤ DM ω) ∧
        (∀ n, ∀ᵐ ω ∂P, |Bmesh n ω| ≤ DB ω) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Ymesh n ω) atTop (nhds (Y ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω))) ∧
        (∀ n, (∫ ω, Mmesh n ω ∂P) = 0) ∧
        (∀ n, (∫ ω, Bmesh n ω ∂P) ≤ 0) ∧
        (∀ᵐ ω ∂P, ∀ n, Ymesh n ω ≤ K + Mmesh n ω + Bmesh n ω) := by sorry
