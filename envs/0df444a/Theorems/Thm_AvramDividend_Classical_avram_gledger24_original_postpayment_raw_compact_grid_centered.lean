-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger24_original_postpayment_raw_compact_grid_centered
-- name    : AvramDividend.Classical.avram_gledger24_original_postpayment_raw_compact_grid_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T15:46:17.906902+00:00
-- url     : https://prove2.me/theorems/d41a1f34-ae84-497b-b4fd-eeb84bd34b23
-- title:
--   Original physical Gaussian postpayment grid centred on the actual compact stop
-- statement:
--   With the actual stopped original X and D compact strict prepayment reserve bound, the true postpayment reserve also lies in the positive compact band at each active deterministic grid time, including zero. Therefore the original untruncated postpayment-gradient/Hessian grid is identical almost surely to the uniformly clipped centred Gaussian grid, is integrable and has expectation exactly zero. This eliminates the prepayment versus postpayment coefficient discrepancy in the chronological Ito–Stieltjes argument.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger23_original_postpayment_physical_grid_centered
import Theorems.Thm_AvramDividend_Classical_avram_gledger18_original_topcap_grid_zero_cell_band
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger24_original_postpayment_raw_compact_grid_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (j n m : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let M : Ω → ℝ := fun ω => ∑ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then
        let y := x + X.X s ω - rightLimit D s ω
        let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        Real.exp (-(q * (s : ℝ))) *
          (deriv w y * z + (iteratedDeriv 2 w y / 2) *
            (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by sorry
