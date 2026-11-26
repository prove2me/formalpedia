-- Prove2me | Theorems.Thm_BKAR_Forest_localRecursiveBoundaryRemainder_eq_zero_of_forall_child_activeEdges_eq_empty
-- name    : BKAR.Forest.localRecursiveBoundaryRemainder_eq_zero_of_forall_child_activeEdges_eq_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:47:07.624995+00:00
-- url     : https://prove2.me/theorems/011a6900-7300-5a6c-bed4-71c51e483aab
-- title:
--   Forest: local Recursive Boundary Remainder eq zero of forall child active Edges eq empty
-- statement:
--   If every first child of a local node is already terminal, the local recursive
--   boundary remainder vanishes.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L59-L73
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L59-L73

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.localRecursiveBoundaryRemainder_eq_zero_of_forall_child_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (choices F e).forest.activeEdges = ∅) :
    localRecursiveBoundaryRemainder choices F pref prefixTs top ρ = 0 := by sorry
