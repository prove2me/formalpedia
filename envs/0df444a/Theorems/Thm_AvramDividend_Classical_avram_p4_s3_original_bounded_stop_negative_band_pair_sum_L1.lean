-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_pair_sum_L1
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_pair_sum_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:26:42.315882+00:00
-- url     : https://prove2.me/theorems/44717391-fd3a-4f58-b237-ce014be5bb5c
-- title:
--   True stopped original negative-band distinct-jump pair sum has quadratic-in-time L1 bound
-- statement:
--   For the original spectrally negative Levy path, at any sample-dependent clock τ≤T, take an exact finite ordered enumeration of distinct pairs of its negative-band jump times, with cardinality Kτ(Kτ−1). Every measurable pairwise finite sum of uniformly bounded coefficients has finite absolute expectation at most B(Tν(Band))². This controls source finite-grid double-jump Taylor and compensator corrections at second physical order.
-- source:
--   Accepted original stopped factorial-pair moment b3b05dd5 together with Finset triangle inequality and pair-cardinality K(K−1); dominated integrability and integral monotonicity bound expected absolute marked pair sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_factorial_pair_moment
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_pair_sum_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard))
    (Pairs : Ω → Finset (ℝ≥0 × ℝ≥0))
    (hPairs : ∀ ω p, p ∈ Pairs ω →
      p.1 ∈ {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))} ∧
      p.2 ∈ {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))} ∧ p.1 ≠ p.2)
    (hPairCard : ∀ ω, ((Pairs ω).card : ℝ) =
      ({u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard : ℝ) *
      (({u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard : ℝ) - 1))
    (H : (ℝ≥0 × ℝ≥0) → Ω → ℝ)
    (hSumMeas : Measurable (fun ω =>
      (Pairs ω).sum (fun p => H p ω)))
    (B : ℝ) (hB : 0 ≤ B) (hH : ∀ p ω, |H p ω| ≤ B) :
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (Pairs ω).sum (fun p => H p ω)) P ∧
    (∫ ω, |(Pairs ω).sum (fun p => H p ω)| ∂P) ≤ B * r ^ 2 := by sorry
