-- Prove2me | Theorems.Thm_ContinuousExpectation_cdfExpectation_eq_integral_pdf
-- name    : ContinuousExpectation.cdfExpectation_eq_integral_pdf
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:17:44.749822+00:00
-- url     : https://prove2.me/theorems/e64fa0c8-a6df-4e8f-adc4-15e002f75ca6
-- title:
--   Source theorem: ContinuousExpectation.cdfExpectation_eq_integral_pdf
-- statement:
--   Exact source-backed Lean theorem ContinuousExpectation.cdfExpectation_eq_integral_pdf from ProbabilityTheory.chapter_01.def_1_3. The proposition and assumptions are preserved in the formal statement. The original proof remains in the pinned source project.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_3.lean#L539

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F000
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic


/-
  Definition of expectation and variance in terms of Riemann-Stieltjes integral.
-/

noncomputable section

end  -- noncomputable section

noncomputable section DiscreteExpectation

namespace DiscreteExpectation

-----------------------------------------------------------------------------
-- 1. BASE CASE: The Zero Integrator (Required for Finset Induction)
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- 2. FINITE SUM INDUCTION (Bridging Thm 1.3 to arbitrary m)
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- 3. THE ANALYTIC STEP FUNCTION HELPER
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- 4. THE MAIN RESULT: Expectation of discreteCDF is a finite sum
-----------------------------------------------------------------------------

end DiscreteExpectation  -- namespace
end DiscreteExpectation  -- section

section ContinuousExpectation

namespace ContinuousExpectation

theorem cdfExpectation_eq_integral_pdf
    {a b : ℝ} {F pdf : ℝ → ℝ}
    (hab : a < b)
    (hFmono : Monotone F)
    (hFderiv : ∀ x ∈ Set.Icc a b, HasDerivAt F (pdf x) x)
    (hpdf_cont : ContinuousOn pdf (Set.Icc a b))
    (h_int : RSIntegrable (fun x => x) F a b) :
    cdfExpectation a b F h_int = ∫ x in a..b, x * pdf x := by sorry

end ContinuousExpectation  -- namespace
end ContinuousExpectation    -- section
