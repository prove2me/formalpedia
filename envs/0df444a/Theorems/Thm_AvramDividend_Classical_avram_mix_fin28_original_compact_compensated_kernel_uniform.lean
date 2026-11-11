-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin28_original_compact_compensated_kernel_uniform
-- name    : AvramDividend.Classical.avram_mix_fin28_original_compact_compensated_kernel_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T15:16:37.041077+00:00
-- url     : https://prove2.me/theorems/86bc48a7-d659-4f84-933e-a4fe91adee6e
-- title:
--   Original finite-mixed compensated kernel uniformly bounded for every negative mark on compact reserve bands
-- statement:
--   Under exactly the original positive-cap mixed finite-activity HJB and reward gradient hypotheses, for any 0<u<v<C choose a nonnegative finite B such that for every y in [u,v) and every negative jump z, the absolute original generator integrand is bounded by B. Import the Proved source compact Gaussian derivative absolute bound 9afa1813, reward upper bound 395ef91e, landing positivity 29c0a475 and the exact compensated kernel bound 0fafc6be; take B=w(v)+K. This directly supplies the L-infinity mark integrand needed for the finite-intensity original filtered stopped-jump martingale in the physical child 52a16569, without a large-mark absolute moment theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_source_compact_absolute_gradient_bound
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_reward_upper_by_interior_cap
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_reward_nonnegative_below_interior
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin28_original_compensated_kernel_absolute_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin28_original_compact_compensated_kernel_uniform
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
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y ∈ Ico u v, ∀ z : ℝ, z < 0 →
        |SpectrallyNegativeLevy.generatorIntegrand w y z| ≤ B := by sorry
