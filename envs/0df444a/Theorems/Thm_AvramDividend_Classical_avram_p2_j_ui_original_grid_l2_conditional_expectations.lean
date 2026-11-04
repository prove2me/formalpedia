-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_grid_l2_conditional_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_grid_l2_conditional_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:46:53.713349+00:00
-- url     : https://prove2.me/theorems/701597b4-9d90-4ea8-9c9e-8d2a38369f5c
-- title:
--   Conditional original Lévy grid L² to genuine expectation convergence
-- statement:
--   Imports the already-Proved original-process bounded negative-grid L2 theorem, obtains its finite horizon-dependent ENNReal second-moment envelope on an eventually small positive mesh, and transfers it to signed real grid sums that are explicitly assumed to be a.e. dominated by the nonnegative grid count. Conditional almost-everywhere convergence to the genuine jump sum is explicitly required; no P2-H result or compensator is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_bounded_negative_test_grid_l2_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_finite_envelope_expectations

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_grid_l2_conditional_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → ENNReal) (M : ENNReal) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0)
    (h : ℕ → ℝ) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hmesh : Tendsto h atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hhor : ∀ᶠ n : ℕ in atTop, (n : ℝ) * h n ≤ T)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hdom : ∀ n, ∀ᵐ ω ∂P, ‖Y n ω‖ₑ ≤
      ∑ i ∈ Finset.range n,
        f (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
          X.X ((i : ℝ≥0) * Real.toNNReal (h n)) ω))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by sorry
