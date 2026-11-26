-- Prove2me | Theorems.Thm_BKAR_Forest_localBoundarySupportOrderContribution_def
-- name    : BKAR.Forest.localBoundarySupportOrderContribution_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:59:11.283154+00:00
-- url     : https://prove2.me/theorems/0ddcadb5-0d4a-5b1e-b1a0-1c89866e86da
-- title:
--   Forest: local Boundary Support Order Contribution def
-- statement:
--   The Forest construction uses the local Boundary Support Order Contribution def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L132-L150
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L132-L150

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.localBoundarySupportOrderContribution_def
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    localBoundarySupportOrderContribution choices F pref prefixTs top I order ρ =
      Finset.sum
        (F.activeEdges.attach.filter
          (fun e =>
            (choices F e).forest.support = I ∧
              pref ++ [e.val] = order))
        (fun e =>
          orderedSimplexIntegralAux top [e.val]
            (fun ts => mixedPartialList order.reverse ρ
              ((choices F e).forest.standardInterp
                ((choices F e).forest.paramsOfOrder order
                  (prefixTs ++ ts))))) := by sorry
