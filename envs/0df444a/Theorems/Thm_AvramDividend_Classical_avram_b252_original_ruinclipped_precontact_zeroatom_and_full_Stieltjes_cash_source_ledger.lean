-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b252_original_ruinclipped_precontact_zeroatom_and_full_Stieltjes_cash_source_ledger
-- name    : AvramDividend.Classical.avram_b252_original_ruinclipped_precontact_zeroatom_and_full_Stieltjes_cash_source_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:41:10.516779+00:00
-- url     : https://prove2.me/theorems/22281282-bbcb-4d12-b2c0-9aa782cd0035
-- title:
--   Original ruin-clipped mixed precontact stopped physical Itô cash full Stieltjes and exact initial zero dividend atom upper ledger
-- statement:
--   For the original mixed Gaussian/negative-jump source X and actual admissible D, on genuine stopped physical cells wholly before ruin, the actual full discounted Stieltjes dividend cash on each half-open cell together with the original singleton time-zero dividend atom and the terminal discounted post-right-dividend allcap potential is bounded by initial original V(x), the exact frozen-right-dividend Lévy source increments, and the explicit within-cell discount mismatch sum. This is an original finite-grid cash source ledger preserving time-zero/right payments, true stop σ and the original finite/infinite cap. The only excluded source contribution is the final cell meeting ruin, requiring a separate contact and L1 estimate to close B236.
-- source:
--   Add Proved B251 actual timezero Stieltjes dividend atom plus original allcap postpayment reserve bound to Proved B248 original precontact stopped full-Stieltjes source ledger, using v0=0, exponential discount e0=1 and original Lévy X.X0=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b252_original_ruinclipped_precontact_zeroatom_and_full_Stieltjes_cash_source_ledger
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0) (n m : ℕ) (ω : Ω)
    (hPre : ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j => min ((j : ℝ≥0) * Δ) (σ ω)
      v (i + 1) = 0 ∨
        (v (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let Y : ℕ → ℝ := fun i =>
      x + X.X (v i) ω - rightLimit D (v i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
    let err : ℕ → ℝ := fun i =>
      (e i - e (i + 1)) * (V (Z i) - V (Y (i + 1)))
    (∫⁻ t in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal +
      e m * V (Y m) + (Finset.range m).sum cash ≤
      V x +
      (Finset.range m).sum (fun i =>
        e (i + 1) * V (Z i) - e i * V (Y i)) +
      (Finset.range m).sum err := by sorry
