-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_sqrt_le_of
-- name    : Formalism.FourierDecayAlt.P.BudgetLiftBounds.sqrt_le_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:57.404802+00:00
-- url     : https://prove2.me/theorems/3f5f46a6-1f01-46ef-9e70-b652561c7c33
-- title:
--   Budget Lift Bounds: sqrt le of
-- statement:
--   The Budget Lift Bounds construction uses the sqrt le of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetLiftSquareRoot.lean#L90-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetLiftSquareRoot.lean#L90-L98

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

theorem Formalism.FourierDecayAlt.P.BudgetLiftBounds.sqrt_le_of {x c d L : ℝ} (hx : x ≤ c * L) (hc0 : 0 ≤ c) (hcd : c ≤ d ^ 2) (hd : 0 ≤ d) :
    √x ≤ d * √L := by sorry
