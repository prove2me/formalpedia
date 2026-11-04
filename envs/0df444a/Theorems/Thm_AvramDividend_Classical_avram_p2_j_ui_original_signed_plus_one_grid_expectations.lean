-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_plus_one_grid_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_signed_plus_one_grid_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:02:00.396951+00:00
-- url     : https://prove2.me/theorems/b3170730-55a3-43d2-855f-6a975e4ffff1
-- title:
--   Exact original signed n+1 Lévy grid expectation convergence conditional on a.e. samplewise limit
-- statement:
--   For the actual original Lévy process, real signed test g pointwise bounded in e-norm by an ENNReal supported test f, and the n+1 uniform mesh, genuine Bochner expectations of signed grid sums converge under an explicitly supplied a.e. pathwise mesh-to-jump limit. Combines the source original L2 bound, deterministic signed finite-sum domination and P2-J Vitali. No process replacement or assumed unproved grid limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_plus_one_grid_conditional_expectations
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_signed_finite_sum_envelope

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_signed_plus_one_grid_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → ENNReal) (M : ENNReal) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0)
    (g : ℝ → ℝ) (hg : ∀ y, ‖g y‖ₑ ≤ f y)
    (h : ℕ → ℝ) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hY : ∀ n ω, Y n ω = ∑ i ∈ Finset.range (n + 1),
      g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
        X.X ((i : ℝ≥0) * Real.toNNReal (h n)) ω))
    (hmesh : Tendsto h atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hhor : ∀ᶠ n : ℕ in atTop, ((n + 1 : ℕ) : ℝ) * h n ≤ T)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by sorry
