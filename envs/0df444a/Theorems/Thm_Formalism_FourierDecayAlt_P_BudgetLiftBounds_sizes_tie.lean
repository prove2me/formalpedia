-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_sizes_tie
-- name    : Formalism.FourierDecayAlt.P.BudgetLiftBounds.sizes_tie
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:55.637051+00:00
-- url     : https://prove2.me/theorems/e24acad2-4b4f-42a4-9b71-520b642b2cba
-- title:
--   Budget Lift Bounds: sizes tie
-- statement:
--   The Budget Lift Bounds construction uses the sizes tie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetLiftSquareRoot.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetLiftSquareRoot.lean#L48-L55

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

theorem Formalism.FourierDecayAlt.P.BudgetLiftBounds.sizes_tie {E : Type} [Field E] (D : Data E) (Pat3 : Type) [Fintype Pat3] (c1 : E → ℝ)
    (c3 : ℕ → E → ℝ) (ep1 : ℝ) (ep3 bd4 : ℕ → ℝ) (ep a : ℝ) (i : ℕ)
    (h : LevelSizes D Pat3 c1 c3 ep1 ep3 bd4 ep a i) : 0 ≤ ep1 ∧ 1 + ep1 ≤ (1 + ep) ^ 2 := by sorry
