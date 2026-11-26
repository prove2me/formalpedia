-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiberIntegrable_of_nontrivialIntegrable
-- name    : BKAR.Forest.boundarySupportOrderTreeFiberIntegrable_of_nontrivialIntegrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:33.7278+00:00
-- url     : https://prove2.me/theorems/b1c90282-9c1d-45c4-a911-b186ef163371
-- title:
--   Forest: boundary Support Order Tree Fiber Integrable of nontrivial Integrable
-- statement:
--   The Forest construction uses the boundary Support Order Tree Fiber Integrable of nontrivial Integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L337-L395
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L337-L395

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiberIntegrable_of_nontrivialIntegrable
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      boundarySupportOrderTreeFiberNontrivialIntegrable choices n
        F pref prefixTs top ρ →
      boundarySupportOrderTreeFiberIntegrable choices n
        F pref prefixTs top ρ
  := by sorry
