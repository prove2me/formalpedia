-- Prove2me | Theorems.Thm_BitDFT_shared_alphabet_sequence
-- name    : BitDFT.shared_alphabet_sequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T22:24:38.253419+00:00
-- url     : https://prove2.me/theorems/064ea8d6-66ce-483f-a72c-a20dc1216193
-- title:
--   Sequential child and multiplier runs cost the two runtimes plus one handoff
-- statement:
--   Suppose the child stage halts after s steps and the multiplier stage, started from the exact handoff configuration, runs for u steps. The composed finite machine reaches the multiplier stage's exact final configuration after at most s+1+u steps. The extra one is the charged transition between stages; all tape contents and head positions pass through unchanged.
-- source:
--   Specialization of the accepted finite-controller sequencing theorem to the published common-alphabet child/multiplier program. The stage-specific run theorems supply exact executions in this common layout.

import Definitions.Def_BitDFT_SharedAlphabetComposition
import Theorems.Thm_BitDFT_machine_sequence_bound
set_option autoImplicit false
open IntMul BitDFT.SharedAlphabetComposition

theorem BitDFT.shared_alphabet_sequence (A M : MultitapeTM) (c : (leftStage A M).Cfg) (s u : ℕ)
    (hhalt : ((leftStage A M).step^[s] c).state = (leftStage A M).qHalt)
    (d : ((second A M).machine).Cfg)
    (hsecond : (second A M).machine.step^[u] (handoff A M ((leftStage A M).step^[s] c)) = d) :
    ∃ t : ℕ, t ≤ s + 1 + u ∧
      (program A M).machine.step^[t] (start A M c) = finish A M d := by sorry
