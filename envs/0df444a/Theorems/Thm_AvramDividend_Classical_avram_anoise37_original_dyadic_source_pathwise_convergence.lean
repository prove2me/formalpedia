-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise37_original_dyadic_source_pathwise_convergence
-- name    : AvramDividend.Classical.avram_anoise37_original_dyadic_source_pathwise_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:26:07.808736+00:00
-- url     : https://prove2.me/theorems/5d14ecdf-811a-41db-97d4-fde5cde8e3b3
-- title:
--   Exact original dyadic signed compensated marked source converges physically
-- statement:
--   Pathwise almost-sure source identity under the original process for the dyadic finite-band marked counts. The original intrinsic compensated source at t minus s is the limit of the finite simple signed marked grid, with no auxiliary process or unidentified filtration.
-- source:
--   Genuine conjunct of Open root-connected ebfd1029 (anoise36). The companion anoise38 completes the separated physical L1 obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise37_original_dyadic_source_pathwise_convergence
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
      (∀ᵐ ω ∂P, Tendsto (fun k => M k ω) atTop
        (𝓝 (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω))) := by sorry
