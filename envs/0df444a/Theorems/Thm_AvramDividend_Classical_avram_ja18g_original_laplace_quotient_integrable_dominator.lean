-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_laplace_quotient_integrable_dominator
-- name    : AvramDividend.Classical.avram_ja18g_original_laplace_quotient_integrable_dominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T04:03:45.289935+00:00
-- url     : https://prove2.me/theorems/c57e222a-6a66-440b-be62-4d0d1a9725e6
-- title:
--   Original process Laplace difference quotient has integrable uniform local dominator
-- statement:
--   For the ORIGINAL spectrally negative Lévy process with Standing, at a fixed t, the positive right-neighbourhood of zero admits an integrable real dominator of the exponential quotient. The quotients are almost everywhere strongly measurable, and the original normalised difference of the moment generating integral agrees with the integral of the pointwise quotient. Split negative X using (1-exp(-a))≤a and positive X using theta≤1/2 and the exponential moment at theta=1. The required bound is integrable from original X fixed-time L1 and positive exponential moments; do not assume an auxiliary Brownian process or jump first-moment beyond Standing.
-- source:
--   J-A18 original analytic expectation derivative integrable control

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_laplace_quotient_integrable_dominator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      let F : ℝ → Ω → ℝ := fun θ ω =>
        (Real.exp (θ * X.X t ω) - 1) / θ
      ∃ bound : Ω → ℝ,
        Integrable bound P ∧
        (∀ᶠ θ in nhdsWithin (0 : ℝ) (Ioi 0),
          AEStronglyMeasurable (F θ) P) ∧
        (∀ᶠ θ in nhdsWithin (0 : ℝ) (Ioi 0),
          ∀ᵐ ω ∂P, ‖F θ ω‖ ≤ bound ω) ∧
        (∀ᶠ θ in nhdsWithin (0 : ℝ) (Ioi 0),
          ((∫ ω, Real.exp (θ * X.X t ω) ∂P) - 1) / θ =
            ∫ ω, F θ ω ∂P) := by sorry
