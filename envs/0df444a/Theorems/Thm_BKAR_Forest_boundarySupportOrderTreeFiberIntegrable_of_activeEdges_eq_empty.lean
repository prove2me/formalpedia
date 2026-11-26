-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiberIntegrable_of_activeEdges_eq_empty
-- name    : BKAR.Forest.boundarySupportOrderTreeFiberIntegrable_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:48:58.830267+00:00
-- url     : https://prove2.me/theorems/00f5e7dc-726f-5838-9ff9-e2a59a3b5be3
-- title:
--   Forest: boundary Support Order Tree Fiber Integrable of active Edges eq empty
-- statement:
--   The Forest construction uses the boundary Support Order Tree Fiber Integrable of active Edges eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L228-L246
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L228-L246

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiberIntegrable_of_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges = ∅ →
      boundarySupportOrderTreeFiberIntegrable choices n
        F pref prefixTs top ρ
  := by sorry
