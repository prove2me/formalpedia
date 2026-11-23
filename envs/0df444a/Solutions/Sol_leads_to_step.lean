-- Prove2me | solution 1 for leads_to_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:41:43.308801+00:00
-- url     : https://prove2.me/submissions/386df280-35a4-4886-95e2-5b63a97cf575

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Temporal

set_option autoImplicit true
open Function Set Filter Stream'
variable {X : Type*} {xs : Stream' X}
theorem _root_.solution {p q : Set X}
    (h : Step xs p q) : LeadsTo xs p q := by
  intro k h_p
  use (k + 1) ; constructor
  · omega
  · exact h k h_p
