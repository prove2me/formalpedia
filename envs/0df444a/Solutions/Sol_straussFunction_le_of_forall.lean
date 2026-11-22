-- Prove2me | solution 1 for straussFunction_le_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:41:05.737743+00:00
-- url     : https://prove2.me/submissions/820e5e9b-a1b3-4428-9e12-08e549479c8a

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction

set_option autoImplicit true
open Finset
theorem _root_.solution {k m : ℕ}
    (h : ∀ S : Finset ℤ, m ≤ #S → HasPolychromColouring (Fin k) S) :
    straussFunction k ≤ m := Nat.sInf_le h
