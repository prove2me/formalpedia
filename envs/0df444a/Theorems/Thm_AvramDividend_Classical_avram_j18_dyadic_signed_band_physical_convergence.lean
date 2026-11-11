-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_j18_dyadic_signed_band_physical_convergence
-- name    : AvramDividend.Classical.avram_j18_dyadic_signed_band_physical_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:29:38.714504+00:00
-- url     : https://prove2.me/theorems/eb7e9ad1-5a60-493e-a948-bb587d532529
-- title:
--   Original finite-activity dyadic signed-band sums converge to the physical compensated source
-- statement:
--   For the actual original marked jump process, dyadic left-endpoint signed finite-cell compensated sums over (s,t] converge almost surely to the literal source compensated negative-mark increment. The deterministic coefficient error is at most 2^-k and original finite count and ν(B) are finite; strict endpoints match the source definition.
-- source:
--   The physical marked-measure identification and approximation half of Open ebfd1029, separate from uniform L1 domination. Use the proved dyadic coefficient lemma fa09a0a9 once accepted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_j18_dyadic_signed_band_physical_convergence
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
      ∀ᵐ ω ∂P, Tendsto (fun k => M k ω) atTop
        (𝓝 (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω)) := by sorry
