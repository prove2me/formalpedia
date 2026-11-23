-- Prove2me | Theorems.Thm_Comp_ModelData_exists_forall_enabled_iff
-- name    : Comp.ModelData.exists_forall_enabled_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:23:45.716718+00:00
-- url     : https://prove2.me/theorems/c82898c4-f484-4698-8f57-68ff96baa579
-- title:
--   Model Data: exists forall enabled iff
-- statement:
--   Restricting `∃ a1, ∀ a2` to the actions a state actually enables.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L686-L701
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L686-L701

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.exists_forall_enabled_iff (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (P : Fin d.nAct1 → Fin d.nAct2 → Prop)
    (hP : ∀ a1 a2, P (d.padFin1 hs s a1) (d.padFin2 hs s a2) ↔ P a1 a2) :
    (∃ a1, ∀ a2, P a1 a2) ↔ (∃ a1 ∈ d.enabled1 hs s, ∀ a2 ∈ d.enabled2 hs s, P a1 a2) := by sorry
