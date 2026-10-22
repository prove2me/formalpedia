-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_past_residual_future_joint_factorisation
-- name    : AvramDividend.Classical.chat06_past_residual_future_joint_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:45:29.885108+00:00
-- url     : https://prove2.me/theorems/c7cd842d-fad5-4260-8e3e-78e8ded26da6
-- title:
--   Joint residual survival and independent whole-future-suffix factorisation
-- statement:
--   If the entire observed-past/current-wait pair is independent of a complete future sequence having common law mu, then a measurable observed-past survival event together with any measurable future event factorises. Its residual-time factor c is an explicit hypothesis, allowing later substitution of the proved Exp(1) memorylessness factor. This is a joint finite-past and infinite-future renewal bridge, while the proof that actual Poisson index-selection events satisfy the premises remains a separate task.
-- source:
--   Source bv_joint_residual_survival_and_future_suffix_factorisation_chat06_20261021.lean (79 lines), SHA-256 9bc74747502c846ca3d0881603ad3f6d25f1cf2e3711690a940589130593f30c, pinned revision 0df444a360eaa60ab8c11dca51a86af692955474. Private probe job 6aca4aac-1679-4b05-aa09-07ea0b7e42c8 reached its sentinel with zero source errors.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Linarith

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_past_residual_future_joint_factorisation
    {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → E) (τ : Ω → ℝ) (Fut : Ω → F)
    (hInd : IndepFun (fun ω => (Z ω, τ ω)) Fut P)
    (μ : Measure F) (hLaw : HasLaw Fut μ P)
    (age : E → ℝ) (hAge : Measurable age)
    (D : Set E) (hD : MeasurableSet D)
    (B : Set F) (hB : MeasurableSet B)
    (t : ℝ) (c : ℝ≥0∞)
    (hResidual :
      P {ω | Z ω ∈ D ∧ age (Z ω) + t < τ ω} =
        P {ω | Z ω ∈ D ∧ age (Z ω) < τ ω} * c) :
    P {ω | (Z ω ∈ D ∧ age (Z ω) + t < τ ω) ∧ Fut ω ∈ B} =
      (P {ω | Z ω ∈ D ∧ age (Z ω) < τ ω} * c) * μ B := by sorry
