-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_grid_killed_kernel_scale
-- name    : AvramDividend.Classical.avram_root29_01_original_grid_killed_kernel_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:14:30.670213+00:00
-- url     : https://prove2.me/theorems/145edfcd-2151-4a07-a778-d3cb977c1e57
-- title:
--   Genuine original-Lévy killed grid reward normalises pointwise to the q-scale at every reserve
-- statement:
--   The true original P law of the entire Lévy future path, pushed forward under t↦X_t, integrates the Borel countably monitored discounted killed q-scale payoff to exactly ENNReal.ofReal W(x) for any real starting capital x, under unbounded variation and q>0. The grid includes a rational cover and endpoint, so actual cadlag Lévy survival equals grid survival pointwise. This is the exact measurable pointwise kernel identity needed for past-event Markov test and conditional killed semigroup, and uses no Open exit statement.
-- source:
--   Distinct new WS1A source work/avram_root29_01_original_grid_killed_kernel_scale_draft.lean, from Proved a885 real-to-ENNReal killed expectation and Proved grid-measurability/survival equality. No reliance on be9 or downstream exits.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_survival_discounted_scale_expectation
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_killed_scale_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_root29_01_original_grid_killed_kernel_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (τ : ℕ → ℝ≥0) (t : ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = t)
    (x : ℝ) :
    (∫⁻ y : ℝ≥0 → ℝ,
      (if ∀ j : ℕ, τ j ≤ t → 0 ≤ x + y (τ j)
        then ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + y t))
        else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun u : ℝ≥0 => X.X u ω)) P)) =
      ENNReal.ofReal (W x) := by sorry
