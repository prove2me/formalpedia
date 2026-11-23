-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_wsup_le
-- name    : Formalism.FourierDecayAlt.P.BudgetLiftBounds.wsup_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:59.207241+00:00
-- url     : https://prove2.me/theorems/e5eb59a8-fd1c-4bd4-bdee-724a4f2519c6
-- title:
--   Budget Lift Bounds: wsup le
-- statement:
--   The Budget Lift Bounds construction uses the wsup le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetLiftSquareRoot.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetLiftSquareRoot.lean#L85-L88

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

theorem Formalism.FourierDecayAlt.P.BudgetLiftBounds.wsup_le {W : Type} (len : W → ℕ) (B : ℕ) (g : W → ℝ) (M : ℝ) (w0 : W) (h0 : len w0 ≤ B)
    (h : ∀ w, len w ≤ B → g w ≤ M) : wsup len B g ≤ M := by sorry
