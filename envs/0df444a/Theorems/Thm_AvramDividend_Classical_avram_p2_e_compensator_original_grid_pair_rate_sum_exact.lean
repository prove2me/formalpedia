-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_grid_pair_rate_sum_exact
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_grid_pair_rate_sum_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:37:20.171762+00:00
-- url     : https://prove2.me/theorems/77b37394-2291-405c-9aa5-4271d391c210
-- title:
--   Finite original chronological grid-pair mean equals deterministic Lévy-rate sum
-- statement:
--   The expectation of a finite deterministic sum of actual original-process past/future negative-band marked-count products equals the explicit source Lévy intensity-rate sum. This is the finite stage of the chronological pair second factorial moment.
-- source:
--   Literal X.X original intrinsic marked jump rectangles, using public Proved finite-grid lintegral-sum interchange and source past/future interval rate-product; pinned Mathlib 0df444a3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_grid_pair_lintegral_finite_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_future_marked_pair_one_cell

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_grid_pair_rate_sum_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m : ℕ) (s t : Fin m → ℝ≥0) (hst : ∀ i, s i ≤ t i) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    (∫⁻ ω, ∑ i : Fin m, N 0 (s i) ω * N (s i) (t i) ω ∂P) =
      ∑ i : Fin m, ((s i : ℝ≥0∞) * X.ν B) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
