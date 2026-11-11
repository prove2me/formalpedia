-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger18_original_topcap_grid_zero_cell_band
-- name    : AvramDividend.Classical.avram_gledger18_original_topcap_grid_zero_cell_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:26:17.146752+00:00
-- url     : https://prove2.me/theorems/a746e0ad-196c-4f98-873c-4be6978a4027
-- title:
--   Original Gaussian stopped grid compact band includes the zero cell
-- statement:
--   For the original dividend-controlled reserve, the positive-time almost-sure compact prefix condition implies the entire active deterministic mesh is contained in a compact band bounded below by min(x,1/(j+1)). At the exceptional time-zero cell, X(0)=D(0)=0 and the reserve is x. This genuine boundary localisation is needed to show the actual Gaussian derivative coefficients have uniform bounds on all stopped cells of ad7f605e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger18_original_topcap_grid_zero_cell_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j n m : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1))
      s < ρ ω →
        riskProcess X x D s ω ∈
          Icc (min x ((1 : ℝ) / ((j : ℝ) + 1)))
            (x + ((j : ℝ) + 1)) := by sorry
