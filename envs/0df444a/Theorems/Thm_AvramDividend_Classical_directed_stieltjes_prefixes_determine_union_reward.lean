-- Prove2me | Theorems.Thm_AvramDividend_Classical_directed_stieltjes_prefixes_determine_union_reward
-- name    : AvramDividend.Classical.directed_stieltjes_prefixes_determine_union_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:44:06.082145+00:00
-- url     : https://prove2.me/theorems/06484432-13ea-4b4a-bdff-eb1f84cfabb7
-- title:
--   Directed surviving Stieltjes prefixes determine the entire stopped positive-time reward
-- statement:
--   For arbitrary two measures and nonnegative weighted dividends, equality of their restricted Lebesgue-Stieltjes integrals on each member of a countable directed family of surviving time prefixes implies equality on the union. The proof passes through monotone convergence of restricted lower integrals. It is the exact bridge needed to exhaust zero-barrier stopped dividend payments by surviving prefixes without moving the ruin endpoint.
-- source:
--   Mathlib MeasureTheory.setLIntegral_iUnion_of_directed, for Avram, Palmowski and Pistorius (2007), section 3.3 zero-barrier Stieltjes reward.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.directed_stieltjes_prefixes_determine_union_reward
    {α : Type*} [MeasurableSpace α]
    {ι : Type*} [Countable ι]
    (μ ν : Measure α) (f : α → ℝ≥0∞) (s : ι → Set α)
    (hd : Directed (fun (a b : Set α) => a ⊆ b) s)
    (hPrefix : ∀ i : ι,
      (∫⁻ x in s i, f x ∂μ) = (∫⁻ x in s i, f x ∂ν)) :
    (∫⁻ x in ⋃ i, s i, f x ∂μ) =
      (∫⁻ x in ⋃ i, s i, f x ∂ν) := by sorry
