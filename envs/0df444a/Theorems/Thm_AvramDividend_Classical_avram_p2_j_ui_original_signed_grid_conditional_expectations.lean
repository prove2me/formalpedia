-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_grid_conditional_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_signed_grid_conditional_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:01:40.903206+00:00
-- url     : https://prove2.me/theorems/d3c64ec3-e0e0-4202-9def-bf90e699dfb0
-- title:
--   Original signed Lévy mesh-grid expectation convergence conditional on a.e. mesh limit
-- statement:
--   A direct original-process application: for a signed test g whose e-norm is bounded pointwise by a supported nonnegative test f, the already proved original Lévy uniform bounded-grid L2 theorem plus the finite-sum triangle inequality imply convergence of genuine signed-grid expectations, conditional on measurable Y and explicitly assumed a.e. grid limit. The theorem requires the actual Lévy process and the original grid increments, with no replacement law or unproved P2-H statement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_grid_l2_conditional_expectations
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_signed_finite_sum_envelope

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_signed_grid_conditional_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → ENNReal) (M : ENNReal) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0)
    (g : ℝ → ℝ) (hg : ∀ y, ‖g y‖ₑ ≤ f y)
    (h : ℕ → ℝ) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hY : ∀ n ω, Y n ω = ∑ i ∈ Finset.range n,
      g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
        X.X ((i : ℝ≥0) * Real.toNNReal (h n)) ω))
    (hmesh : Tendsto h atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hhor : ∀ᶠ n : ℕ in atTop, (n : ℝ) * h n ≤ T)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by sorry
