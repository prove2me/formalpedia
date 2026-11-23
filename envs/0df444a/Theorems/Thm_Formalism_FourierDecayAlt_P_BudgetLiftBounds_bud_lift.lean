-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_bud_lift
-- name    : Formalism.FourierDecayAlt.P.BudgetLiftBounds.bud_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:02.553284+00:00
-- url     : https://prove2.me/theorems/8840526b-6f82-4be6-8aa2-ed1d5c45d824
-- title:
--   Budget Lift Bounds: bud lift
-- statement:
--   The Budget Lift Bounds construction uses the bud lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetLiftSquareRoot.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetLiftSquareRoot.lean#L9-L16

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

theorem Formalism.FourierDecayAlt.P.BudgetLiftBounds.bud_lift (Kl r i n : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ r + 1) (hn : n ≤ 4 * Kl * (r + 1 - i)) :
    n + Kl ≤ 4 * Kl * (r + 1) := by sorry
