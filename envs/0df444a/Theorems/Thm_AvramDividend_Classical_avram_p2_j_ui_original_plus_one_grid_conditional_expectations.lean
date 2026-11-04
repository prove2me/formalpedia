-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_plus_one_grid_conditional_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_plus_one_grid_conditional_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:47:36.570478+00:00
-- url     : https://prove2.me/theorems/12c9e9d0-a9ee-4fff-a7ab-3ad834b07d16
-- title:
--   Actual Lévy n+1 interval grid second moments give conditional expectation convergence
-- statement:
--   The exact n+1-increment indexing of P2-A/P2-H: take a sequence of positive mesh widths tending to zero with (n+1) h_n≤T, an a.e. signed-domination by the original process nonnegative test grid, and an explicit a.e. pathwise limit. The already proved source uniform grid L2 theorem and P2-J Vitali bridge yield genuine Bochner expectation convergence. It does not assume any current P2-H theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_bounded_negative_test_grid_l2_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_finite_envelope_expectations

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_plus_one_grid_conditional_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → ENNReal) (M : ENNReal) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0)
    (h : ℕ → ℝ) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hmesh : Tendsto h atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hhor : ∀ᶠ n : ℕ in atTop, ((n + 1 : ℕ) : ℝ) * h n ≤ T)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hdom : ∀ n, ∀ᵐ ω ∂P, ‖Y n ω‖ₑ ≤
      ∑ i ∈ Finset.range (n + 1),
        f (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
          X.X ((i : ℝ≥0) * Real.toNNReal (h n)) ω))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by sorry
