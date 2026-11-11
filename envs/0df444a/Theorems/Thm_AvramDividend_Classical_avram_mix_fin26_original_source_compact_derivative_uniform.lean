-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_source_compact_derivative_uniform
-- name    : AvramDividend.Classical.avram_mix_fin26_original_source_compact_derivative_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:05:00.011891+00:00
-- url     : https://prove2.me/theorems/0f6512a2-c48f-4d0d-9a29-af4d8f2ff8c4
-- title:
--   Source-exact original finite mixed HJB reward has a uniformly bounded derivative on each compact interior interval
-- statement:
--   Bridge the original spectrally-negative mixed X generator HJB, original finite cap domain, gradient >=1, w(0)>=0 and negative-side zero extension to the analytic derivative comparison. The two already-proven boundary lemmas imply nonnegative reward at every negative jump landing and w(y)<=w(v) for u<=y<v. The finite-intensity generator inequality and Gronwall control then give a constant B bounding w' on [u,v). Explicit nonnegative β,ε satisfying the displayed drift/forcing comparison are retained; these are elementary choices when the positive Gaussian variance is given.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_finite_cap_derivative_uniform
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_reward_nonnegative_below_interior
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_reward_upper_by_interior_cap
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin26_original_source_compact_derivative_uniform
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (q u v β ε : ℝ) (hq : 0 < q) (hu : 0 < u) (huv : u < v)
    (hvC : ENNReal.ofReal v < C)
    (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (hA : 0 < X.σ ^ 2 / 2)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hBeta : -X.c ≤ (X.σ ^ 2 / 2) * β)
    (hEps : (q + (X.ν (Iio (0 : ℝ))).toReal) * w v ≤
      (X.σ ^ 2 / 2) * ε) :
    ∃ B : ℝ, ∀ y ∈ Ico u v, deriv w y ≤ B := by sorry
