-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise41_original_dyadic_physical_mark_count_convergence
-- name    : AvramDividend.Classical.avram_anoise41_original_dyadic_physical_mark_count_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:16:11.40468+00:00
-- url     : https://prove2.me/theorems/3d81e41d-5627-4946-b909-856bf452abfa
-- title:
--   Physical finite dyadic marked jump counts converge to original uncompensated band increments
-- statement:
--   Original-space finite-activity jump count simple sums approximate the signed jump sum in the original intrinsic compensated band. Uses the already Proved finite-jump representation and endpoint mark error; no auxiliary stochastic processes.
-- source:
--   Necessary original physical count half of Open h37 (5d14ecdf), complementing deterministic compensator approximation h42.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise41_original_dyadic_physical_mark_count_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ n : ℕ, ∀ T : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) P) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ C k i)
      (∀ᵐ ω ∂P, Tendsto
        (fun k => ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) * (J k i ω).toReal)
        atTop
        (𝓝 ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω) +
          (((t - s : ℝ≥0) : ℝ) *
            (∫ z in B, z ∂X.ν))))) := by sorry
