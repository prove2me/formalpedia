-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_true_original_caplinear_full_precontact_physical_grid_signed_cash_nonpos
-- name    : AvramDividend.Classical.avram_f6_true_original_caplinear_full_precontact_physical_grid_signed_cash_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T21:53:32.842889+00:00
-- url     : https://prove2.me/theorems/4b0482ba-ed1f-43a0-816f-6fdbf1dbda60
-- title:
--   Original mixed all-cap finite physical precontact Stieltjes cash plus cap-linear postpayment corrections nonpositive
-- statement:
--   For any genuine spectrally negative Lévy process and an admissible capped dividend strategy, any finite monotone physical time grid whose right endpoints are zero or strictly precede original ruin satisfies a source-faithful signed inequality. The sum of the complete discounted Stieltjes dividend cash on each original mesh cell and the weighted negative cap-linear postpayment potential corrections is nonpositive. The cap-linear V is the actual extension of w beyond the dividend cap, so prepayment reserve overshoots above C are handled correctly, even with Gaussian and infinite-activity negative jumps. The result follows by adding the existing Proved original one-cell full Stieltjes source sign b240, and is a valid finite-grid source for the stopped Itô verification. The ruin-contact final cell is excluded and must be proved separately.
-- source:
--   Proved original full-stieltjes signed one-cell physical source b240 fe0b56a6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_f6_true_original_caplinear_full_precontact_physical_grid_signed_cash_nonpos
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
    (∑ i ∈ Finset.range m,
      ((∫⁻ t in Ioc (v i : ℝ) (v (i + 1) : ℝ),
         ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
       Real.exp (-(q * (v i : ℝ))) *
        (V (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
         V (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤ 0 := by sorry
