-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_source_compact_absolute_gradient_bound
-- name    : AvramDividend.Classical.avram_mix_fin26_original_source_compact_absolute_gradient_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:29:12.687497+00:00
-- url     : https://prove2.me/theorems/9afa1813-323d-4248-85cc-fde5a9a11cbf
-- title:
--   Original mixed finite-cap HJB supplies an absolute gradient bound for local Gaussian Itô integrands
-- statement:
--   Under exactly the original mixed finite-jump HJB and gradient hypotheses and for each 0<u<v strictly below the cap, there is a nonnegative K bounding abs(deriv w(y)) uniformly for y in [u,v). Import the Proved original-source compact derivative upper bound and combine it with the original 1<=deriv w lower bound. This is the deterministic L-infinity weight needed for local Gaussian stochastic integrability, excluding any global near-zero derivative assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_source_compact_derivative_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin26_original_source_compact_absolute_gradient_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (q u v : ℝ) (hq : 0 < q) (hu : 0 < u) (huv : u < v)
    (hvC : ENNReal.ofReal v < C)
    (hσ : X.σ ≠ 0)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ Ico u v, |deriv w y| ≤ K := by sorry
