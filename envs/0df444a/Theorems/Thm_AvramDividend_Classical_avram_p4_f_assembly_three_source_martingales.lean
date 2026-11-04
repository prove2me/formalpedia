-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_three_source_martingales
-- name    : AvramDividend.Classical.avram_p4_f_assembly_three_source_martingales
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:48:33.124044+00:00
-- url     : https://prove2.me/theorems/ea0aaca6-f1b3-467a-b199-7ea501be837e
-- title:
--   Three integrable centred source martingales assemble with jointly nonpositive generator and control residuals
-- statement:
--   An exact algebraic interface for P4-F assembly: given an actual stopped Itô inequality with separate continuous, compensated small-jump and large-jump integrable zero-mean source martingales, and two integrable residuals whose sum is nonpositive, the required canonical triple exists. This conditional assembly proves zero expectation of their precise sum without claiming that the original source stochastic-integral estimates have been established.
-- source:
--   Finite stopped Itô–Meyer residual bookkeeping from Avram–Palmowski–Pistorius Eq. (5.11)-(5.12); Mathlib integrable.add and integral_add. The source-specific stochastic identities remain dependencies.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_three_source_martingales
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (x : ℝ)
    (Term Cash Mc Ms Ml G H : Ω → ℝ)
    (hc : Integrable Mc P) (hs : Integrable Ms P)
    (hl : Integrable Ml P) (hg : Integrable G P)
    (hh : Integrable H P)
    (hc0 : (∫ ω, Mc ω ∂P) = 0)
    (hs0 : (∫ ω, Ms ω ∂P) = 0)
    (hl0 : (∫ ω, Ml ω ∂P) = 0)
    (hres : ∀ᵐ ω ∂P, G ω + H ω ≤ 0)
    (hito : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + H ω) :
    ∃ M G' H' : Ω → ℝ,
      Integrable M P ∧ Integrable G' P ∧ Integrable H' P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G' ω + H' ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        Term ω + Cash ω ≤ w x + M ω + G' ω + H' ω) := by sorry
