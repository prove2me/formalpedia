-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_levy_X_laplace_quotient_to_triplet
-- name    : AvramDividend.Classical.avram_ja18g_original_levy_X_laplace_quotient_to_triplet
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T03:26:08.428922+00:00
-- url     : https://prove2.me/theorems/cd53a52a-c198-4907-908a-33eebbe503d8
-- title:
--   Original Levy-Khintchine Laplace quotient converges to triplet first moment
-- statement:
--   Compute the right derivative of the exact original exponential Levy-Khintchine identity. The Gaussian quadratic term and compensated small negative jumps are o(theta), while the original negative large mark term has first derivative its signed Levy integral. The exponential outer factor contributes time t.
-- source:
--   J-A18 original X first moment Laplace derivative bridge

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_levy_X_laplace_quotient_to_triplet
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      Filter.Tendsto
        (fun θ : ℝ =>
          ((∫ ω, Real.exp (θ * X.X t ω) ∂P) - 1) / θ)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds ((t : ℝ) * (X.c + (∫ z in Iic (-1 : ℝ), z ∂X.ν)))) := by sorry
