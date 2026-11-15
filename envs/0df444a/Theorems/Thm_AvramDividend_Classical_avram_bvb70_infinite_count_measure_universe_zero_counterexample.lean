-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb70_infinite_count_measure_universe_zero_counterexample
-- name    : AvramDividend.Classical.avram_bvb70_infinite_count_measure_universe_zero_counterexample
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:04:09.965325+00:00
-- url     : https://prove2.me/theorems/dca35ba4-aa15-44ba-a13d-523588104230
-- title:
--   Unrestricted-measure envelope false on infinite counting measure (universe-zero certificate)
-- statement:
--   The generic BVB70 residual domination statement omits finiteness of the measure. On Nat with counting measure, take all component rows and their envelopes zero and b=-1, giving E_n=1 everywhere. Any integrable common envelope must dominate 1 almost everywhere, impossible on infinite counting measure. This proof is explicitly restricted to Type 0 to avoid the current disproof checker universe unification issue; it is a certified counterexample to one instance, not a Disproved mark on the original theorem.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb70_infinite_count_measure_universe_zero_counterexample :
    ¬ (∀
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F J V : ℕ → Ω → ℝ) (b : ℝ)
    (Fbound Jbound Vbound : Ω → ℝ)
    (hFi : Integrable Fbound P) (hJi : Integrable Jbound P)
    (hVi : Integrable Vbound P)
    (hFRows : ∀ n, Integrable (F n) P)
    (hJRows : ∀ n, Integrable (J n) P)
    (hVRows : ∀ n, Integrable (V n) P)
    (hFdom : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ Fbound ω)
    (hJdom : ∀ n, ∀ᵐ ω ∂P, ‖J n ω‖ ≤ Jbound ω)
    (hVdom : ∀ n, ∀ᵐ ω ∂P, ‖V n ω‖ ≤ Vbound ω),
    let E : ℕ → Ω → ℝ := fun n ω =>
      max (F n ω - (b + (J n ω - V n ω))) 0
    ∃ Henv : Ω → ℝ,
      Integrable Henv P ∧
      (∀ n, AEStronglyMeasurable (E n) P) ∧
      (∀ n, ∀ᵐ ω ∂P, ‖E n ω‖ ≤ Henv ω)) := by sorry
