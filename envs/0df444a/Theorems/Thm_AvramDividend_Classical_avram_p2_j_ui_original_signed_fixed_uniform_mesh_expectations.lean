-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_fixed_uniform_mesh_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_signed_fixed_uniform_mesh_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:22:09.677902+00:00
-- url     : https://prove2.me/theorems/982f90b4-6bb0-4e4d-bc62-98312305e412
-- title:
--   Genuine signed original Lévy test sums on exact positive uniform n+1 mesh: expectation convergence under a.e. limit
-- statement:
--   For the actual spectrally negative Lévy X, positive horizon T and a signed test g dominated by a supported nonnegative f, prove integrability of the genuine jump-sum limit and convergence of signed real expectations of the explicit original n+1 mesh at T/(n+1), conditional only on grid measurability and a.e. pathwise convergence. Mesh positivity and the horizon equation are proved, not assumed; no compensated law or Lévy rate premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_plus_one_grid_expectations
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_positive_plus_one_mesh_horizon

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_signed_fixed_uniform_mesh_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 < T)
    (f : ℝ → ENNReal) (M : ENNReal) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0)
    (g : ℝ → ℝ) (hg : ∀ y, ‖g y‖ₑ ≤ f y)
    (Z : Ω → ℝ)
    (hm : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
           X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω)) P)
    (hae : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
           X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω))
      atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n : ℕ => ∫ ω,
          (∑ i ∈ Finset.range (n + 1),
            g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
               X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω)) ∂P)
        atTop (nhds (∫ ω, Z ω ∂P)) := by sorry
