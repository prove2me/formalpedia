-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_coord8_t10_equalcell_marked_product_stationary_mean
-- name    : AvramDividend.Classical.avram_coord8_t10_equalcell_marked_product_stationary_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:30:27.590402+00:00
-- url     : https://prove2.me/theorems/4292bced-0ee6-4e2e-ac5d-85d0df5dda50
-- title:
--   Stationary expectation of original marked-jump products across equal cells
-- statement:
--   For every equal cell the source-original strict negative-jump exponential product has the same expectation as its first-cell counterpart. The result isolates stationarity of marked increments from independence.
-- source:
--   Exact decomposition obligation for open source Avram theorem a657c8d2-c004-4cd0-9591-191c8a08fb10; the complementary generic independent equal-mean product lemma is ca7ab513-deed-488f-93c4-7e4935c7ffc9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_coord8_t10_equalcell_marked_product_stationary_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let J : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let C : Fin (n + 1) → Ω → ℝ := fun i ω =>
      ∏ u ∈ (J ω).filter (fun u =>
        (i.val : ℝ≥0) * T < u ∧ u ≤ ((i.val : ℝ≥0) + 1) * T),
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    ∀ i : Fin (n + 1),
      (∫ ω, C i ω ∂P) =
        (∫ ω, ∏ u ∈ S ω,
          Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P) := by sorry
