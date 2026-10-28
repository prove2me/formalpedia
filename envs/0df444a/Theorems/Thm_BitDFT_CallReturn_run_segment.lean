-- Prove2me | Theorems.Thm_BitDFT_CallReturn_run_segment
-- name    : BitDFT.CallReturn.run_segment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T02:19:54.028668+00:00
-- url     : https://prove2.me/theorems/7bcb86f1-87ba-47db-b315-f2e891a77109
-- title:
--   Compose one exact call and return segment
-- statement:
--   Let a controller P reach its call state after a steps without halting or visiting that state earlier. Let the called controller Q then run for b steps from its entry configuration to its exit state, with no earlier visit to the exit. The composed controller performs the dispatch and return transitions as part of the run, so the exact total is a+1+b+1 steps and the final tape contents and head positions are precisely those of Q's exit configuration, with P's resume state restored.
-- source:
--   Exact finite-controller call/return composition lemma for repeated multiplier-backed record processing in BitDFT.rescale_output_machine.

import Definitions.Def_BitDFT_CallReturn
import Mathlib.Logic.Function.Iterate
set_option autoImplicit false
open IntMul

theorem BitDFT.CallReturn.run_segment {M : MultitapeTM}
    (P Q : BitDFT.MachineSequence.Controller M)
    (call resume : P.K) (hcall : call ≠ P.exit)
    (c : P.machine.Cfg) (a b : ℕ)
    (hPavoid : ∀ s < a, (P.machine.step^[s] c).state ≠ P.exit ∧
      (P.machine.step^[s] c).state ≠ call)
    (hCall : (P.machine.step^[a] c).state = call)
    (hQavoid : ∀ s < b,
      (Q.machine.step^[s] (enterQ P Q call resume (P.machine.step^[a] c))).state ≠ Q.exit)
    (hQexit : (Q.machine.step^[b]
      (enterQ P Q call resume (P.machine.step^[a] c))).state = Q.exit) :
    (machine P Q call resume hcall).step^[a + 1 + b + 1]
      (fromP P Q call resume hcall c) =
    fromP P Q call resume hcall
      (returnP P Q call resume
        (Q.machine.step^[b] (enterQ P Q call resume (P.machine.step^[a] c)))) := by sorry
