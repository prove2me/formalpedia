-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_divisionQuotientFormula
-- name    : ClassicalComplexWPT.analyticAt_divisionQuotientFormula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:04:56.43038+00:00
-- url     : https://prove2.me/theorems/268c9aab-252a-4025-a15e-c1bccaa47601
-- title:
--   Classical Complex WPT: analytic At division Quotient Formula
-- statement:
--   The Classical Complex WPT construction uses the analytic At division Quotient Formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L318-L325
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L318-L325

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]

theorem ClassicalComplexWPT.analyticAt_divisionQuotientFormula (d : ℕ)
    (pf : L1Coeff (A × ℕ) × L1Coeff (A × ℕ)) (hp : ‖pf.1‖ < 1) :
    AnalyticAt ℂ (fun x ↦ Ring.inverse (1 + divisionOperatorInput d x)
      (divisionRhsInput d x)) pf := by sorry
