-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_levy_X_laplace_quotient_to_mean
-- name    : AvramDividend.Classical.avram_ja18g_original_levy_X_laplace_quotient_to_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T03:25:57.780931+00:00
-- url     : https://prove2.me/theorems/d8e75b25-a746-4e54-8d31-22b6a57b46fb
-- title:
--   Original Laplace quotient converges to original first moment
-- statement:
--   Differentiate E[e^(theta X_t)] at theta=0 from the right by truncating sample paths and applying L1 dominated convergence. Standing gives X_t integrability and the positive exponential moment. The original probability P and X are unchanged.
-- source:
--   J-A18 original X first moment Laplace derivative bridge

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_levy_X_laplace_quotient_to_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      Filter.Tendsto
        (fun θ : ℝ =>
          ((∫ ω, Real.exp (θ * X.X t ω) ∂P) - 1) / θ)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (∫ ω, X.X t ω ∂P)) := by sorry
