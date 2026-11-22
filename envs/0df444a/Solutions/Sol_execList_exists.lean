-- Prove2me | solution 1 for execList_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:46.924038+00:00
-- url     : https://prove2.me/submissions/757e353c-8496-4c77-85c3-69fdb4135e7b

import Definitions.Def_EventStructures_Family_Path
import Mathlib.Data.Set.Card
import Definitions.Def_EventStructures_Family_Reachability
import Theorems.Thm_path_exists

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
theorem _root_.solution {c₀ c : Conf F} (hsub : c₀.val ⊆ c.val)
    (hfin : (c.val \ c₀.val).Finite) :
    Nonempty (Σ t : List F.Event, Path.ExecList F c₀ t c) := by
  obtain ⟨p⟩ := path_exists F hsub hfin
  exact ⟨⟨Path.trace F p, Path.execList_of_path F p⟩⟩
