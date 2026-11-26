-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeContribution_eq_zero_of_activeEdges_eq_empty
-- name    : BKAR.Forest.boundarySupportOrderTreeContribution_eq_zero_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:16:59.654224+00:00
-- url     : https://prove2.me/theorems/2776efe8-b28d-4cbe-9d2a-ae69e0a43a71
-- title:
--   Forest: boundary Support Order Tree Contribution eq zero of active Edges eq empty
-- statement:
--   The Forest construction uses the boundary Support Order Tree Contribution eq zero of active Edges eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L172-L184
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L172-L184

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeContribution_eq_zero_of_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hF : F.activeEdges = ∅) :
    boundarySupportOrderTreeContribution choices F pref prefixTs top ρ = 0 := by sorry
