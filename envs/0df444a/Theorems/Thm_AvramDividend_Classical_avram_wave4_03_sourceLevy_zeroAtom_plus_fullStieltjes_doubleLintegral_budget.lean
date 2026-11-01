-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_zeroAtom_plus_fullStieltjes_doubleLintegral_budget
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_zeroAtom_plus_fullStieltjes_doubleLintegral_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:20:42.717784+00:00
-- url     : https://prove2.me/theorems/b5e6d927-91dd-4a1f-8055-a465638228c7
-- title:
--   Original Lévy actual full Stieltjes finite-step stochastic double-integral budget including time zero
-- statement:
--   For the original same-path adapted Lévy and nondecreasing control, the expected true time-zero right Stieltjes atom plus the expected full random-measure Stieltjes double integral on every finite half-open mesh cell, weighted by the compensated Lévy exponential and full postpayment dividend discount, is ≤1. The positive-time integration includes diffuse and singular-continuous mass, not only right payment jumps.
-- source:
--   Exact full random Stieltjes cell integral to cash identity 8358e91d and new true initial atom plus finite-grid ENNReal cash budget 11934d73.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_fullStieltjes_cellIntegral_eq_finiteGrid_cashENNReal
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_lintegral_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_zeroAtom_plus_fullStieltjes_doubleLintegral_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u)
    (hu0 : u 0 = 0) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω) ∂P) +
    (∫⁻ ω, ∫⁻ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        ENNReal.ofReal (θ * Real.exp
          (θ * X.X (u (i + 1)) ω -
            (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω)))
      else 0 ∂dividendMeasure D ω ∂P) ≤ 1 := by sorry
