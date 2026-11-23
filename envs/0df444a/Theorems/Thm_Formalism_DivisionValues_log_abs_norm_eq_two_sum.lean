-- Prove2me | Theorems.Thm_Formalism_DivisionValues_log_abs_norm_eq_two_sum
-- name    : Formalism.DivisionValues.log_abs_norm_eq_two_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:55.766519+00:00
-- url     : https://prove2.me/theorems/2a5125fc-330d-4c5f-bfdf-683bf46eba33
-- title:
--   Division Values: log abs norm eq two sum
-- statement:
--   The Division Values construction uses the log abs norm eq two sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ProdFormula.lean#L22-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ProdFormula.lean#L22-L37

import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.DivisionValues

theorem Formalism.DivisionValues.log_abs_norm_eq_two_sum (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (a : K) (ha : a ≠ 0) :
    Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| =
      2 * ∑ v : InfinitePlace K, Real.log ‖v.embedding a‖ := by sorry
