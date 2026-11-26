-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeContribution_def
-- name    : BKAR.Forest.boundarySupportOrderTreeContribution_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:00:43.066556+00:00
-- url     : https://prove2.me/theorems/0acb356f-8554-525c-9382-94fb0faf6885
-- title:
--   Forest: boundary Support Order Tree Contribution def
-- statement:
--   The Forest construction uses the boundary Support Order Tree Contribution def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L160-L170
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L160-L170

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeContribution_def
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    boundarySupportOrderTreeContribution choices F pref prefixTs top ρ =
      localBoundarySupportOrderSum choices F pref prefixTs top ρ +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            boundarySupportOrderTreeContribution choices
              (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ) := by sorry
