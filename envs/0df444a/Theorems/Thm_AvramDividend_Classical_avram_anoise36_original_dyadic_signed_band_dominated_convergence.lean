-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise36_original_dyadic_signed_band_dominated_convergence
-- name    : AvramDividend.Classical.avram_anoise36_original_dyadic_signed_band_dominated_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:55:46.811192+00:00
-- url     : https://prove2.me/theorems/5f7ea99e-ac72-4721-9515-cc50e8d5713a
-- title:
--   Original dyadic signed-band sums converge under a common L1 dominator
-- statement:
--   For the literal original marked-jump measure, dyadic finite-simple signed compensators on a fixed negative band converge almost surely to the exact signed compensated increment and are bounded uniformly in dyadic refinement by one integrable original-space function. The finite-activity count gives domination, while simple coefficient approximation and the finite measure of the band supply convergence. This is the precise missing analytic step in 4da238cd after its integrability and conditional centring of every dyadic approximation were already Proved by dd554a61.
-- source:
--   Strict mathematical reduction of 4da238cd-cd5f-4297-ba8b-da96d69000de. Already Proved dd554a61 gives all dyadic M_k integrable and conditionally centred; this child isolates only L1 domination and a.s. convergence of the actual signed dyadic sums. No auxiliary model, no moment on unbounded large marks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise36_original_dyadic_signed_band_dominated_convergence
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
      let M : ℕ → Ω → ℝ := fun k ω =>
        ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
            ((J k i ω).toReal -
              (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
      ∃ bound : Ω → ℝ, Integrable bound P ∧
        (∀ᵐ ω ∂P, Tendsto (fun k => M k ω) atTop
          (𝓝 (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω))) ∧
        (∀ k, ∀ᵐ ω ∂P, ‖M k ω‖ ≤ bound ω) := by sorry
