-- Prove2me | Theorems.Thm_BKAR_Forest_localBoundarySupportOrderSum_eq_zero_of_activeEdges_eq_empty
-- name    : BKAR.Forest.localBoundarySupportOrderSum_eq_zero_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:09.828252+00:00
-- url     : https://prove2.me/theorems/445fcf98-0bcd-48be-af92-0e7c0c0f6897
-- title:
--   Forest: local Boundary Support Order Sum eq zero of active Edges eq empty
-- statement:
--   The Forest construction uses the local Boundary Support Order Sum eq zero of active Edges eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L126-L141
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L126-L141

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.localBoundarySupportOrderSum_eq_zero_of_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hF : F.activeEdges = ∅) :
    localBoundarySupportOrderSum choices F pref prefixTs top ρ = 0 := by sorry
