-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_long_mesh_source_tube_of_native_joint_event
-- name    : AvramDividend.Classical.avram_gaussianB_original_long_mesh_source_tube_of_native_joint_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:56:57.670247+00:00
-- url     : https://prove2.me/theorems/c60bab29-6487-40b4-a5a9-f20b54c75253
-- title:
--   Original Gaussian stopped G/H physical mesh source has genuine centered and drifted bounds through entire 17/16000 overshoot horizon
-- statement:
--   For an actual original drift-two Gaussian Lévy source and canonical Brownian joint-tube event, every source sample t≤17/16000 satisfies the exact original Lévy source identity, centred Brownian bound ≤1/4000 and original source bound ≤1/400. The horizon includes the stopped clock T=1/1000 plus the next physical-grid right endpoint and supplies the exact hLongSource and hLongCentered premises of the Proved B182/B184 original stopped G/H martingale L1 estimate.

import Mathlib.Tactic.NormNum
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_unitInterval_long_tube_uniform_nnreal_lemma
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_original_long_mesh_source_tube_of_native_joint_event
    (𝓕 : Filtration ℝ≥0
      (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
    (Y : SpectrallyNegativeLevy gaussianLimit 𝓕)
    (hpath : ∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
      Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ))
    (E : Set (ℝ≥0 → ℝ))
    (hTube : ∀ ω ∈ E, ∀ s : unitInterval,
      s ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
      |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
      |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω +
        2 * (s : ℝ)| ≤ (1 / 400 : ℝ)) :
    ∀ ω ∈ E, ∀ t : ℝ≥0, t ≤ (17 / 16000 : ℝ≥0) →
      Y.X t ω = (brownian t ω - brownian 0 ω) + 2 * (t : ℝ) ∧
      |brownian t ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
      |Y.X t ω| ≤ (1 / 400 : ℝ) := by sorry
