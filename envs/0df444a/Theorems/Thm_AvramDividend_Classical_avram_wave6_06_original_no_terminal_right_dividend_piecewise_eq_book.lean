-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_no_terminal_right_dividend_piecewise_eq_book
-- name    : AvramDividend.Classical.avram_wave6_06_original_no_terminal_right_dividend_piecewise_eq_book
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:34:42.77509+00:00
-- url     : https://prove2.me/theorems/5cfae94b-7078-44a4-a3b9-4d985bce0881
-- title:
--   Original no-terminal-dividend-atom bridge from source piecewise reserve to literal book reserve
-- statement:
--   If the actual original dividend right increment vanishes at the stopped time on every path, the source-faithful postpayment/book piecewise terminal agrees exactly with the literal original pre-right-payment riskProcess. This is the exact extra endpoint hypothesis needed to replace the source W by U_tau when the cash Stieltjes interval is inclusive at tau; no jump/source stochastic identity is postulated.
-- source:
--   Avram Proposition 4(i), Eq. (5.11)-(5.13); original left-continuous dividend endpoint convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_no_terminal_right_dividend_piecewise_eq_book
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hNoAtom : ∀ ω, rightLimit D (τ ω) ω = D (τ ω) ω) :
    ∀ ω, W ω = riskProcess X x D (τ ω) ω := by sorry
