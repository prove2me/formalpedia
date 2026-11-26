-- Prove2me | Theorems.Thm_BKAR_Forest_localBoundarySupportOrderSum_eq_sum_supportOrderPairs
-- name    : BKAR.Forest.localBoundarySupportOrderSum_eq_sum_supportOrderPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:26.180216+00:00
-- url     : https://prove2.me/theorems/e744b588-29c1-5042-9cff-c373afba2c89
-- title:
--   Forest: local Boundary Support Order Sum eq sum support Order Pairs
-- statement:
--   The Forest construction uses the local Boundary Support Order Sum eq sum support Order Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L397-L406
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L397-L406

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.localBoundarySupportOrderSum_eq_sum_supportOrderPairs
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    localBoundarySupportOrderSum choices F pref prefixTs top ρ =
      Finset.sum (supportOrderPairs V)
        (fun x =>
          localBoundarySupportOrderContribution choices F pref prefixTs top
            x.1 x.2 ρ) := by sorry
