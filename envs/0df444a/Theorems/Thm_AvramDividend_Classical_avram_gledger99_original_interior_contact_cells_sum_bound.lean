-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger99_original_interior_contact_cells_sum_bound
-- name    : AvramDividend.Classical.avram_gledger99_original_interior_contact_cells_sum_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:28:03.459453+00:00
-- url     : https://prove2.me/theorems/da5c2f45-eb9d-4499-9225-be2d17bdc37c
-- title:
--   Original strict stopped grid interior dividend-contact cash sum bound
-- statement:
--   Summing the original real-valued strict interior discounted cash and dividend-contact inequalities over a finite stopped grid preserves the expected rate-times-mass upper bound. Every cell remains strictly before the stopping time and has finite Stieltjes mass. The result is a direct finite-sum closure of already-proved gledger93 and is a genuine interior component of gledger81.
-- source:
--   Strict original-process interior finite-grid summation input for gledger81.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger99_original_interior_contact_cells_sum_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (u : ℝ) (hu : 0 ≤ u)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      u ≤ riskProcess X x D t ω)
    (v : ℕ → ℝ≥0) (hv : Monotone v) (k : ℕ)
    (hinterior : ∀ i : ℕ, i < k → v (i + 1) < ρ)
    (hfinite : ∀ i : ℕ, i < k →
      dividendMeasure D ω (Ioc (v i : ℝ) (v (i + 1) : ℝ)) ≠ ⊤)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    (Finset.sum (Finset.range k) (fun i =>
      (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (v (i + 1) : ℝ))) *
        (w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
          w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤
      Finset.sum (Finset.range k) (fun i =>
        q * ((v (i + 1) : ℝ) - (v i : ℝ)) *
          (dividendMeasure D ω (Ioc (v i : ℝ) (v (i + 1) : ℝ))).toReal) := by sorry
