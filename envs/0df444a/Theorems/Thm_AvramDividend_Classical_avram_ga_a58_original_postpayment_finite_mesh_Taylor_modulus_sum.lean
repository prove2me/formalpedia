-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a58_original_postpayment_finite_mesh_Taylor_modulus_sum
-- name    : AvramDividend.Classical.avram_ga_a58_original_postpayment_finite_mesh_Taylor_modulus_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T19:00:26.974957+00:00
-- url     : https://prove2.me/theorems/f5496974-5a0b-4b42-bc2d-016336658e4f
-- title:
--   Finite-sum C2 remainder bound on the original postpayment stopped Gaussian mesh
-- statement:
--   For the actual X and rightLimit dividend D, on any finite collection of postpayment cells whose starting and target values stay inside a fixed positive compact band, uniformly small source increments force the sum of second-order Taylor remainders to be bounded by epsilon times their total square energy. This is the physical deterministic Taylor estimate needed in the original interior Gaussian positive-L1 limit b0d9951c.
-- source:
--   Proved exact original postpayment C2 Taylor modulus 71f47e40; physical Gaussian interior b0d9951c and original mesh oscillation a56.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_postpayment_C2_taylor_remainder_modulus
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a58_original_postpayment_finite_mesh_Taylor_modulus_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (ω : Ω) (S : Finset ℕ) (s : ℕ → ℝ≥0) (y : ℕ → ℝ),
        let z : ℕ → ℝ := fun i =>
          x + X.X (s i) ω - rightLimit D (s i) ω
        (∀ i ∈ S, z i ∈ Icc a b ∧ y i ∈ Icc a b ∧
          z i ≠ y i ∧ dist (y i) (z i) < δ) →
        |∑ i ∈ S, (w (y i) -
          taylorWithinEval w 1 (uIcc (z i) (y i)) (z i) (y i) -
          (iteratedDeriv 2 w (z i) * (y i - z i) ^ 2) / 2)| ≤
        ε * ∑ i ∈ S, (y i - z i) ^ 2 := by sorry
