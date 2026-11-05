-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_paid_atom_residual_nonpos_no_secant
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_finite_paid_atom_residual_nonpos_no_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:44:14.556376+00:00
-- url     : https://prove2.me/theorems/e76f6622-bf23-4df7-aff0-5dff7b8be5cf
-- title:
--   Finite genuine original paid right-dividend atom corrections nonpositive without a local secant bound
-- statement:
--   For every finite collection of genuine original paid dividend atoms, the original right-jump residuals have nonpositive total discounted sign using only the canonical right-jump hypothesis. The Proved paymentTimes dichotomy handles time zero and strictly pre-ruin physical times, including horizon payments before ruin and excluding positive ruin atoms. No uniform local secant constant K is required for this finite-budget statement. Infinite paid-atom summability and integrability remain separate obligations.
-- source:
--   Public P4-D 9f4070e7 original pointwise discounted right-dividend residual nonpositivity; public a7a447fa paymentTimes exact zero/strictly-pre-ruin dichotomy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_finite_paid_atom_residual_nonpos_no_secant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D s ω - D s ω ≤
          w (riskProcess X x D s ω) -
            w (riskProcess X x D s ω -
              (rightLimit D s ω - D s ω)))
    (ω : Ω) (t : ι → ℝ) (S : Finset ι)
    (hPay : ∀ i ∈ S, t i ∈ paymentTimes (ruinTime X x D ω)) :
    (∑ i ∈ S, Real.exp (-(q * t i)) *
      ((rightLimit D (Real.toNNReal (t i)) ω -
        D (Real.toNNReal (t i)) ω) +
        w (x + X.X (Real.toNNReal (t i)) ω -
          rightLimit D (Real.toNNReal (t i)) ω) -
        w (riskProcess X x D (Real.toNNReal (t i)) ω))) ≤ 0 := by sorry
