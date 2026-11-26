-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_allBranchesAnalytic_of_activeEdges_eq_empty
-- name    : BKAR.BKARContDiff.allBranchesAnalytic_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:53.80983+00:00
-- url     : https://prove2.me/theorems/b7a60247-a06f-4e4d-a952-886cbbda661a
-- title:
--   BKARCont Diff: all Branches Analytic of active Edges eq empty
-- statement:
--   Terminal recursion nodes satisfy `allBranchesAnalytic` at every remaining
--   fuel level once the order bound and global smoothness are available.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L98-L133
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L98-L133

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.allBranchesAnalytic_of_activeEdges_eq_empty
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ),
      F.activeEdges = ∅ →
      (∀ t ∈ Set.uIcc 0 top, ∀ e : F.EdgeParam,
        t ≤ F.paramsOfOrder pref prefixTs e) →
      Forest.allBranchesAnalytic choices n F pref prefixTs top ρ
  := by sorry
