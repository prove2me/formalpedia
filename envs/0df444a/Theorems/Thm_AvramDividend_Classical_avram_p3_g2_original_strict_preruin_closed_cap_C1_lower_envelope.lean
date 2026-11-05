-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_strict_preruin_closed_cap_C1_lower_envelope
-- name    : AvramDividend.Classical.avram_p3_g2_original_strict_preruin_closed_cap_C1_lower_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:45:49.549202+00:00
-- url     : https://prove2.me/theorems/62183577-55d3-4074-8f17-6acd53920377
-- title:
--   Original BV positive-time strict pre-ruin HJB unit-slope lower envelope through closed cap contact
-- statement:
--   At every strictly pre-ruin positive physical time in the original capped spectrally negative Lévy reserve, the HJB C1 gradient bound implies w(riskProcess) >= w(0)+riskProcess, including exact contact with the finite cap. This source-specific quantitative envelope uses only genuine postpayment reserve solvency, the original right-limit dividend jump decomposition, cap admissibility, closed-cap C1 continuity and derivative >=1. It needs no initial-reserve condition, standing, generator drift inequality, HJB equality, moment bound or extra stopping assumption. In particular, combined with w(0)>=0 it supplies the original P3 strict pre-ruin nonnegativity premise.
-- source:
--   From the accepted source proof of capped_admissible_bookReserve_candidate_nonnegative_preRuin cd9655ac and the Proved closed-cap C1 gradient lower envelope fc03f3ac. Strengthens original controlled-reserve interior-only a5bfe0dd to cap contact while dropping standing, initial reserve and interior-cap assumptions. Source exact adapter for P3 original residual hnonneg and P3-F2 stopping boundary.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_strict_preruin_closed_cap_C1_lower_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      w 0 + riskProcess X x D t ω ≤
        w (riskProcess X x D t ω) := by sorry
