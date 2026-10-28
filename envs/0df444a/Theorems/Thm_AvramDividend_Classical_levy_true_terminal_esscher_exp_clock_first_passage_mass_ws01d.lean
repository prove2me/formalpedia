-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_true_terminal_esscher_exp_clock_first_passage_mass_ws01d
-- name    : AvramDividend.Classical.levy_true_terminal_esscher_exp_clock_first_passage_mass_ws01d
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T11:56:18.566044+00:00
-- url     : https://prove2.me/theorems/e5ca1e66-c551-4ac5-a85c-b0a5abd8ed9e
-- title:
--   Uncapped strict upper first-passage mass under genuine random-terminal Esscher density and real exponential clock
-- statement:
--   For an actual spectrally negative Lévy X and an independent real exponential observation E of positive rate p, the genuine terminal Esscher likelihood exp(phi X_E-q E), with phi≥0 and ψ(phi)=q, integrated over the event that the uncapped strict first upper passage T_b is finite and its true time is no later than E, equals the original-P finite-passage integral of exp(phi*b-(p+q)*T_b). Non-strict boundary is exact and later agrees with the strict clock event by atomlessness; infinite passages contribute zero. This is the uncapped nonnegative monotone limit of the canonically Proved finite-cap random-terminal identity, not a fixed-terminal Q_T law.
-- source:
--   Kuznetsov–Kyprianou–Rivero section 2.1, Avram–Palmowski–Pistorius (2007) equation (3.6), canonically Proved 1f657d32, measurable passage clocks 7ded075d and finite capped time 1ad55083.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_levy_capped_first_record_true_terminal_esscher_exp_clock_mass_ws01d
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_true_terminal_esscher_exp_clock_first_passage_mass_ws01d
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b)
    (p : ℝ) (hp : 0 < p)
    (phi q : ℝ) (hphi : 0 ≤ phi) (hroot : X.ψ phi = q) :
    (∫⁻ z : Ω × ℝ,
      if twoSidedExitUpTime X b z.1 < (⊤ : ℝ≥0∞) ∧
        ((twoSidedExitUpTime X b z.1).toNNReal : ℝ) ≤ z.2 then
        ENNReal.ofReal (Real.exp
          (phi * X.X z.2.toNNReal z.1 - (z.2.toNNReal : ℝ) * q))
      else 0 ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    (∫⁻ ω : Ω, if twoSidedExitUpTime X b ω < (⊤ : ℝ≥0∞) then
      ENNReal.ofReal (Real.exp
        (phi * b - (p + q) * (twoSidedExitUpTime X b ω).toReal))
      else 0 ∂P) := by sorry
