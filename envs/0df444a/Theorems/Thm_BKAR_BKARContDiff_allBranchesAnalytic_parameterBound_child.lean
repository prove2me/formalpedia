-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_allBranchesAnalytic_parameterBound_child
-- name    : BKAR.BKARContDiff.allBranchesAnalytic_parameterBound_child
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:20:22.295173+00:00
-- url     : https://prove2.me/theorems/385c4c6f-c2f4-4f97-a7c4-ed011d19dd3f
-- title:
--   BKARCont Diff: all Branches Analytic parameter Bound child
-- statement:
--   The ordered-parameter bound in `allBranchesAnalytic` propagates to a child
--   node after appending the active edge parameter.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L26-L51
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L26-L51

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.allBranchesAnalytic_parameterBound_child
    (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (htop : 0 ≤ top)
    (hbound :
      ∀ t ∈ Set.uIcc 0 top, ∀ e : F.EdgeParam,
        t ≤ F.paramsOfOrder pref prefixTs e)
    (e : {e // e ∈ F.activeEdges}) {t : ℝ}
    (ht : t ∈ Set.uIcc 0 top) :
    ∀ s ∈ Set.uIcc 0 t,
      ∀ e' : (choices F e).forest.EdgeParam,
        s ≤ (choices F e).forest.paramsOfOrder (pref ++ [e.val])
          (prefixTs ++ [t]) e' := by sorry
