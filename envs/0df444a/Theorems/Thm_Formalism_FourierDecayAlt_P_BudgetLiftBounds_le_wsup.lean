-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_le_wsup
-- name    : Formalism.FourierDecayAlt.P.BudgetLiftBounds.le_wsup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:30:37.114197+00:00
-- url     : https://prove2.me/theorems/1db28bd8-fffe-4791-8857-e0a2daae10b4
-- title:
--   Budget Lift Bounds: le wsup
-- statement:
--   The Budget Lift Bounds construction uses the le wsup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetLiftSquareRoot.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetLiftSquareRoot.lean#L81-L83

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

theorem Formalism.FourierDecayAlt.P.BudgetLiftBounds.le_wsup {W : Type} [Finite W] (len : W → ℕ) (B : ℕ) (g : W → ℝ) (w : W) (h : len w ≤ B) :
    g w ≤ wsup len B g := by sorry
