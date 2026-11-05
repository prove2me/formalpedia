-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_drop_unintegrable_nonpositive_control
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_drop_unintegrable_nonpositive_control
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:28:54.108198+00:00
-- url     : https://prove2.me/theorems/1ba0679b-63d6-449f-90d2-d8a8a411655b
-- title:
--   Same-original-process stopped UBV assembly discards favourable control residual without an L1 assumption
-- statement:
--   Given actual original stopped terminal and Cash and a source Ito decomposition into three integrable centred martingales, one integrable nonpositive HJB drift and an a.e. nonpositive control loss of unrestricted L1 size, the corrected three-witness interface holds with H=0. This is a conditional assembly helper, and does not establish the source decomposition or the canonical parent.
-- source:
--   Integrates accepted avram_p4_f_assembly_three_source_martingales with nonpositive-loss elimination for the genuine original W, Cash and Term.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_three_source_martingales
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_drop_unintegrable_nonpositive_control
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
    (Mc Ms Ml G R : Ω → ℝ)
    (hc : Integrable Mc P) (hs : Integrable Ms P)
    (hl : Integrable Ml P) (hg : Integrable G P)
    (hc0 : (∫ ω, Mc ω ∂P) = 0)
    (hs0 : (∫ ω, Ms ω ∂P) = 0)
    (hl0 : (∫ ω, Ml ω ∂P) = 0)
    (hGnonpos : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hRnonpos : ∀ᵐ ω ∂P, R ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R ω) :
    ∃ M G' H' : Ω → ℝ,
      Integrable M P ∧ Integrable G' P ∧ Integrable H' P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G' ω + H' ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        Term ω + Cash ω ≤ w x + M ω + G' ω + H' ω) := by sorry
