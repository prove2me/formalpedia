-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_uniform_mesh_strong_L1
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_signed_uniform_mesh_strong_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:06:02.415067+00:00
-- url     : https://prove2.me/theorems/15d22be3-fe35-4063-ad5b-91f6497ff52e
-- title:
--   Genuine signed original Lévy uniform n+1 mesh converges strongly in L¹ under samplewise convergence
-- statement:
--   For a genuine spectrally negative Lévy process and signed test g dominated by supported bounded ENNReal f, the exact uniform positive mesh T/(n+1) converges strongly in L1 to the actual samplewise jump-test limit when a.e. convergence and measurability are proven. The theorem proves mesh positivity and terminal horizon equality internally, deriving the genuine original process L2 bound, signed grid domination and Vitali L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_plus_one_grid_strong_L1
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_positive_plus_one_mesh_horizon

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_signed_uniform_mesh_strong_L1
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
    MemLp Z 1 P ∧
      Tendsto (fun n : ℕ => eLpNorm
        ((fun ω => ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω -
             X.X ((i : ℝ≥0) * Real.toNNReal (T / ((n : ℝ) + 1))) ω)) - Z)
        1 P) atTop (nhds 0) := by sorry
