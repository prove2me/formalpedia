-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_true_original_caplinear_precontact_right_discount_cash_error_exact
-- name    : AvramDividend.Classical.avram_f6_true_original_caplinear_precontact_right_discount_cash_error_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:02:19.232653+00:00
-- url     : https://prove2.me/theorems/1c8f563f-d511-47e7-9c55-cca642b7284c
-- title:
--   Original physical precontact finite-grid right-discounted cash ledger bounded by exact cap-linear mesh oscillation
-- statement:
--   For the actual spectrally negative Lévy process and capped admissible dividends, a finite pre-ruin physical time grid satisfies the exact right-discounted cash/cap-linear postpayment correction bound. The only error is the sum of the per-cell discount oscillations (E_i−E_(i+1)) times the actual cap-linear prepayment difference V(Z_i)−V(Y_(i+1)). This precisely isolates the discounted physical Stieltjes mesh error and never assumes an unverified O(mesh) rate or evaluates the unconstrained original w outside the cap. Follows by summing the proved original one-cell full Stieltjes estimate b240 and a ring identity; no local Lean compilation or unproved stochastic martingale source is invoked.
-- source:
--   Proved b240 fe0b56a6; original X, D, rightLimit, full physical Stieltjes discount preserved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_f6_true_original_caplinear_precontact_right_discount_cash_error_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (v : ℕ → ℝ≥0) (hv : Monotone v)
    (m : ℕ) (hPre : ∀ i < m,
      v (i + 1) = 0 ∨
        (v (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let E : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
    let B : ℕ → ℝ := fun i =>
      V (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
      V (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)
    let Cash : ℕ → ℝ := fun i =>
      (∫⁻ t in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    (Finset.sum (Finset.range m) (fun i =>
       Cash i + E (i + 1) * B i)) ≤
      (Finset.sum (Finset.range m) (fun i =>
        (E i - E (i + 1)) * (-(B i)))) := by sorry
