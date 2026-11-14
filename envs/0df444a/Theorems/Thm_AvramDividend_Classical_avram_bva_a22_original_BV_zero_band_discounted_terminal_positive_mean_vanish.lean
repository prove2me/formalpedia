-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_zero_band_discounted_terminal_positive_mean_vanish
-- name    : AvramDividend.Classical.avram_bva_a22_original_BV_zero_band_discounted_terminal_positive_mean_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:52:42.443994+00:00
-- url     : https://prove2.me/theorems/32f02858-934d-4278-a161-294df81d7a84
-- title:
--   Original BV discounted true-horizon positive terminal omission has vanishing expected error on the full closed reserve band including zero
-- statement:
--   For the genuine original BV spectrally negative Levy X and original dividend strategy D, assume the verification candidate is monotone and uniformly continuous on a single closed nonnegative reserve band including ruin boundary zero, with a nonnegative true-horizon candidate and row integrability of the explicitly defined positive terminal omission. On original sample paths where both postpayment endpoints remain in the band, the omitted discounted full-T reward beyond the last prescribed strict physical-grid clock has vanishing expected positive error. The proof combines the source-exact one-sided last-cell modulus with a uniform almost-sure epsilon upper bound and the original probability law. No strictly positive spatial floor, global generator L1 or independent surrogate source is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_discounted_terminal_one_sided_modulus
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_uniform_ae_small_positive_error_integral_vanish
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_BV_zero_band_discounted_terminal_positive_mean_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) (B : ℝ)
    (hmono : MonotoneOn w (Icc (0 : ℝ) B))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ Icc (0 : ℝ) B, ∀ z ∈ Icc (0 : ℝ) B,
      |z - y| < δ → |w z - w y| < ε)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Err : ℕ → Ω → ℝ := fun m ω =>
      if (x + X.X (u m (m + 1)) ω -
            rightLimit D (u m (m + 1)) ω) ∈ Icc (0 : ℝ) B ∧
         (x + X.X S ω - rightLimit D S ω) ∈ Icc (0 : ℝ) B ∧
         0 ≤ w (x + X.X S ω - rightLimit D S ω) then
        max (Real.exp (-(q * T)) *
            w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω)) 0
      else 0
    (∀ m, Integrable (Err m) P) →
    Tendsto (fun m => ∫ ω, Err m ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
