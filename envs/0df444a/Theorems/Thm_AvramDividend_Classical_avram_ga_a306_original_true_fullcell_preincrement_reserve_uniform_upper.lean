-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a306_original_true_fullcell_preincrement_reserve_uniform_upper
-- name    : AvramDividend.Classical.avram_ga_a306_original_true_fullcell_preincrement_reserve_uniform_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:45:52.821796+00:00
-- url     : https://prove2.me/theorems/9798fe34-054d-4336-8123-0e81fb327566
-- title:
--   True original stopped Gaussian physical-cell preincrement reserve is bounded by strict prefix localisation ceiling
-- statement:
--   For the genuine controlled spectrally negative Lévy process and actual finite-horizon physical mesh, if the original riskProcess is almost surely bounded above by x+j+1 at all strictly positive times preceding rho, then the postpayment reserve x+X_s-rightLimit D_s is almost surely also at most x+j+1 on every mesh cell starting before rho, including s=0. This uses the proved gledger73 theorem, which already handles time zero, and supplies the compact initial-reserve bound for converting global HJB endpoint exponential into signed Gaussian increment moments in a263.
-- source:
--   Original source riskProcess prefix localization hprefix, gledger73 strict prefix postpayment ceiling, physical finite grid

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gledger73_original_strict_prefix_postpayment_ceiling
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a306_original_true_fullcell_preincrement_reserve_uniform_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let B : ℝ := x + ((j : ℝ) + 1)
    0 ≤ B ∧ ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      s < ρ ω →
        x + X.X s ω - rightLimit D s ω ≤ B := by sorry
