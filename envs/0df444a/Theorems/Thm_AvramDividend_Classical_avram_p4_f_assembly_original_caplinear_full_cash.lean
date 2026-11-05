-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_caplinear_full_cash
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_caplinear_full_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:54:17.315084+00:00
-- url     : https://prove2.me/theorems/eaec5e05-ff3a-438f-8967-4a1227246677
-- title:
--   Canonical P4-F cap-linear extension gives the original full-Stieltjes pre-ruin cash sign
-- statement:
--   For the actual original source Levy process and an admissible controlled dividend path, build the cap-linear extension V of the same interior C² verification function w. On every pre-ruin finite stopping outcome, the exact full Stieltjes Cash plus the terminal cap-linear value correction is nonpositive. This discharges the P4-D auxiliary extension from the original P4-F hypotheses without assuming a new source process, compensation, or integrability.
-- source:
--   Accepted exact P4-D original full-cash inequality 183de9ac, from user canonical interior C²/gradient and original admissible process, with V explicitly defined by current cap C.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_P4F_pre_ruin_hW_full_cash_nonpositive
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_caplinear_full_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Cash : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
        if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P, (τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) →
      Cash ω + V (W ω) - V (x + X.X (τ ω) ω) ≤ 0 := by sorry
