-- Prove2me | Theorems.Thm_BKAR_Forest_sum_localBoundarySupportContribution
-- name    : BKAR.Forest.sum_localBoundarySupportContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:15:10.198359+00:00
-- url     : https://prove2.me/theorems/3501cd18-371a-4671-8708-457dca253b7d
-- title:
--   Forest: sum local Boundary Support Contribution
-- statement:
--   Local active-boundary sectors regroup by child support.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L174-L211
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L174-L211

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_localBoundarySupportContribution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum F.activeEdges.attach
        (fun e =>
          orderedSimplexIntegralAux top [e.val]
            (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
              ((choices F e).forest.standardInterp
                ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                  (prefixTs ++ ts))))) =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I =>
          localBoundarySupportContribution choices F pref prefixTs top I ρ) := by sorry
