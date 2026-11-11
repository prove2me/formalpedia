-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_source_compact_derivative_bound
-- name    : AvramDividend.Classical.avram_mix_fin26_original_source_compact_derivative_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:16:45.570242+00:00
-- url     : https://prove2.me/theorems/c430b75c-e281-4539-bf67-488a1f89785e
-- title:
--   Original finite-mixed HJB directly bounds the derivative on every positive compact interior interval
-- statement:
--   Under the original spectrally negative Levy mixed Gaussian/nonzero finite-jump assumptions, positive q, reward boundary and HJB generator and gradient hypotheses, the first reward derivative is bounded above on every [u,v) with 0<u<v and ofReal(v)<C. This removes the β,ε coefficient comparison assumptions from the already Proved original-source derivative theorem by taking a=σ²/2>0, β=max(0,-c/a), ε=max(0,((q+ν(Iio0).toReal)*w(v))/a), whose nonnegativity and drift/forcing comparisons are elementary real inequalities. No assumption at the positive cap endpoint or large negative-jump first moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_source_compact_derivative_uniform
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin26_original_source_compact_derivative_bound
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
    ∃ B : ℝ, ∀ y ∈ Ico u v, deriv w y ≤ B := by sorry
