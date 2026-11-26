-- Prove2me | Theorems.Thm_BKAR_Forest_localBoundarySupportContribution_def
-- name    : BKAR.Forest.localBoundarySupportContribution_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:59:34.196003+00:00
-- url     : https://prove2.me/theorems/33ae833a-745c-401a-9577-24bfc8f5e5f7
-- title:
--   Forest: local Boundary Support Contribution def
-- statement:
--   The Forest construction uses the local Boundary Support Contribution def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L92-L107
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L92-L107

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.localBoundarySupportContribution_def
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    localBoundarySupportContribution choices F pref prefixTs top I ρ =
      Finset.sum
        (F.activeEdges.attach.filter
          (fun e => (choices F e).forest.support = I))
        (fun e =>
          orderedSimplexIntegralAux top [e.val]
            (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
              ((choices F e).forest.standardInterp
                ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                  (prefixTs ++ ts))))) := by sorry
