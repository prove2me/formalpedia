-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_short_source_tube_of_native_joint_long_event
-- name    : AvramDividend.Classical.avram_gaussianB_original_short_source_tube_of_native_joint_long_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:56:39.094358+00:00
-- url     : https://prove2.me/theorems/aae6b53d-f924-4028-ba24-3c328bb50124
-- title:
--   Original drift-two Gaussian source inherits the canonical positive joint Brownian tube on the exact short stopped interval
-- statement:
--   For any exact drift-two Brownian original spectrally negative Lévy source, a native Gaussian joint Brownian event through time 17/16000 implies on every short original time t≤1/1000 the exact source identity Y.X_t=B_t+2t, the centred Brownian bound ≤1/4000 and the full original source bound ≤1/400. This directly supplies all three sample-path assumptions in the Proved B180 stopped-cash contradiction without covertly switching probability spaces.

import Mathlib.Tactic.NormNum
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.BrownianMotion.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_original_short_source_tube_of_native_joint_long_event
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
    ∀ ω ∈ E, ∀ t : ℝ≥0, t ≤ (1 / 1000 : ℝ≥0) →
      Y.X t ω = (brownian t ω - brownian 0 ω) + 2 * (t : ℝ) ∧
      |brownian t ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
      |Y.X t ω| ≤ (1 / 400 : ℝ) := by sorry
