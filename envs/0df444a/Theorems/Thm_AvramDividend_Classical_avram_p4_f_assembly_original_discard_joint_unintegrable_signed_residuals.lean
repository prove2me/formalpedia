-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_discard_joint_unintegrable_signed_residuals
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_discard_joint_unintegrable_signed_residuals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:34:23.942146+00:00
-- url     : https://prove2.me/theorems/acff23eb-1a44-4ef4-9f9c-e4d53e83454e
-- title:
--   Original-source UBV assembly drops jointly nonpositive generator/control losses without separate L1 bounds
-- statement:
--   If the genuine original stopped Ito-Meyer pathwise budget contains three integrable centered source martingales plus a joint nonpositive generator/control correction, both signed correction terms may be dropped without separate L1 assumptions. The canonical output uses M as the three-martingale sum and G=H=0. This is a conditional algebraic interface, not a proof of the missing source Ito-Meyer pathwise decomposition.
-- source:
--   The genuinely original W, Cash, Term and accepted avram_p4_f_assembly_three_source_martingales; preserves the exact source process while removing unnecessary signed-residual L1 requirements.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_three_source_martingales
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_discard_joint_unintegrable_signed_residuals
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (Mc Ms Ml Rgen Rctrl : Ω → ℝ)
    (hc : Integrable Mc P) (hs : Integrable Ms P)
    (hl : Integrable Ml P)
    (hc0 : (∫ ω, Mc ω ∂P) = 0)
    (hs0 : (∫ ω, Ms ω ∂P) = 0)
    (hl0 : (∫ ω, Ml ω ∂P) = 0)
    (hjoint : ∀ᵐ ω ∂P, Rgen ω + Rctrl ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + Rgen ω + Rctrl ω) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by sorry
