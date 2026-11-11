-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise42_original_dyadic_levy_compensator_approx
-- name    : AvramDividend.Classical.avram_anoise42_original_dyadic_levy_compensator_approx
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:16:09.691419+00:00
-- url     : https://prove2.me/theorems/3df22acc-98b9-4bf5-80db-9c09982100a6
-- title:
--   Dyadic finite negative-mark Lévy compensator converges to original signed band integral
-- statement:
--   The original finite negative Lévy measure compensator is approximated by finite dyadic left-endpoint signed mark sums. Prove integrability on the bounded band and the 2^-k times finite intensity error.
-- source:
--   Necessary deterministic intensity half of Open h37 (5d14ecdf), complementing physical count convergence h41.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise42_original_dyadic_levy_compensator_approx
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
      Tendsto
        (fun k => ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
            ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal))
        atTop
        (𝓝 (((t - s : ℝ≥0) : ℝ) * (∫ z in B, z ∂X.ν))) := by sorry
