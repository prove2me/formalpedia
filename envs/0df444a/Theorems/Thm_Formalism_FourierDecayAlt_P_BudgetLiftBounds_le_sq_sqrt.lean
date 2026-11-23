-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_le_sq_sqrt
-- name    : Formalism.FourierDecayAlt.P.BudgetLiftBounds.le_sq_sqrt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:12.488938+00:00
-- url     : https://prove2.me/theorems/44865751-73a1-4a88-b473-6fc335e19c27
-- title:
--   Budget Lift Bounds: le sq sqrt
-- statement:
--   The Budget Lift Bounds construction uses the le sq sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetLiftSquareRoot.lean#L251-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetLiftSquareRoot.lean#L251-L254

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetLiftSquareRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BudgetLiftBounds

theorem Formalism.FourierDecayAlt.P.BudgetLiftBounds.le_sq_sqrt (x : ℝ) : x ≤ (√x) ^ 2 := by sorry
