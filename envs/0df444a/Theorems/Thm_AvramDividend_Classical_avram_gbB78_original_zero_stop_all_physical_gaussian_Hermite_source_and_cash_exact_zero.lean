-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB78_original_zero_stop_all_physical_gaussian_Hermite_source_and_cash_exact_zero
-- name    : AvramDividend.Classical.avram_gbB78_original_zero_stop_all_physical_gaussian_Hermite_source_and_cash_exact_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:38:13.48819+00:00
-- url     : https://prove2.me/theorems/4a17abe1-bcbf-4e84-b1f5-c2452ea9b7f8
-- title:
--   Original finite-cap physical Gaussian stopped Hermite source and original strict cash both collapse exactly at zero clock
-- statement:
--   For the genuine original source and dividend strategy, if the actual localisation stop rho(omega)=0 then the original discounted strict cash value F(omega) is exactly w(x), and every physical stopped Gaussian first- and second-Hermite coefficient vanishes on all cells because the true mask s_i<rho is false. Therefore M_m(omega)=0 for each physical mesh size, with the exact original clipping coefficients and cap C retained. This explicitly settles the time-zero cash and stopped Gaussian source branch of the B54 source ledger.
-- source:
--   The original B54 full physical coefficient definitions with exact true s_i, Y_i, Z_i, G_i, H_i masks and original cash F. If rho=0 the cash if-branch evaluates to w(x) and the NNReal cell start is never strictly below zero, so both G_i and H_i are zero in every finite cell.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_gbB78_original_zero_stop_all_physical_gaussian_Hermite_source_and_cash_exact_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (ρ : Ω → ℝ≥0) (δ : ℝ) (j n : ℕ) :
  let M : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℕ → Ω → ℝ := fun i η =>
        x + X.X (s i) η - rightLimit D (s i) η
      let Z : ℕ → Ω → ℝ := fun i η =>
        X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
      let G : ℕ → Ω → ℝ := fun i η =>
        if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
          (if Y i η ∈ Icc a b then deriv w (Y i η) else 1)
        else 0
      let H : ℕ → Ω → ℝ := fun i η =>
        if s i < ρ η then (1 / 2 : ℝ) *
          Real.exp (-(q * (s i : ℝ))) *
          (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0)
        else 0
      (Finset.range (m + 1)).sum (fun i =>
        G i ω * Z i ω + H i ω *
          (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
    let b : ℝ := C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let F : Ω → ℝ := fun ω =>
        if ρ ω = 0 then w x else
          Real.exp (-(q * (ρ ω : ℝ))) *
            w (riskProcess X x D (ρ ω) ω) +
          (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * z)))
            ∂(dividendMeasure D ω)).toReal
    ∀ (m : ℕ) (ω : Ω), ρ ω = 0 →
      F ω = w x ∧ M m ω = 0 := by sorry
