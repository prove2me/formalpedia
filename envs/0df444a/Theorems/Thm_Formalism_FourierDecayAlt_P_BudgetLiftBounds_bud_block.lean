-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_bud_block
-- name    : Formalism.FourierDecayAlt.P.BudgetLiftBounds.bud_block
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:59.427127+00:00
-- url     : https://prove2.me/theorems/c34ebbb8-2684-4154-8b08-02faa5feee80
-- title:
--   Budget Lift Bounds: bud block
-- statement:
--   The Budget Lift Bounds construction uses the bud block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetLiftSquareRoot.lean#L32-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BudgetLiftSquareRoot.lean#L32-L46

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

theorem Formalism.FourierDecayAlt.P.BudgetLiftBounds.bud_block (Kl r i s n n' : ℕ) (hs : 2 ≤ s) (hsi : s ≤ i) (h2 : i ≤ r + 1)
    (hn : n ≤ 4 * Kl * (r + 1 - i)) (hn' : n' ≤ n + Kl) :
    n' + (s + 1) * Kl ≤ 4 * Kl * (r + 1 - (i - s)) ∧
      4 * Kl * (r + 1 - (i - s)) ≤ 4 * Kl * (r + 1) := by sorry
