-- Prove2me | solution 1 for orthComp_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:06:35.874761+00:00
-- url     : https://prove2.me/submissions/242baaa5-ba89-4096-ad53-9aaa95fc6ff6

import Mathlib
import Definitions.Def_Basic

set_option autoImplicit true
variable {O : Type*} [Orthoset O]
theorem _root_.solution {X Y : Set O} (h : X ⊆ Y) : orthComp Y ⊆ orthComp X :=
  fun _ hz x hx => hz x (h hx)
