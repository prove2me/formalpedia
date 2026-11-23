-- Prove2me | solution 1 for leads_to_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:41:43.891021+00:00
-- url     : https://prove2.me/submissions/3331a5b0-317b-4fc9-a699-e2d20b0faae9

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Temporal

set_option autoImplicit true
open Function Set Filter Stream'
variable {X : Type*} {xs : Stream' X}
theorem _root_.solution {p q r : Set X}
    (h1 : LeadsTo xs p q) (h2 : LeadsTo xs q r) : LeadsTo xs p r := by
  intro k h_p
  obtain ⟨k', h_k', h_q⟩ := h1 k h_p
  obtain ⟨k'', h_k'', h_r⟩ := h2 k' h_q
  use k'' ; constructor
  · omega
  · assumption
