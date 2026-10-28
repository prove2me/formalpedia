-- Prove2me | Theorems.Thm_BitDFT_CallReturn_call_segment_run
-- name    : BitDFT.CallReturn.call_segment_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T22:51:08.224293+00:00
-- url     : https://prove2.me/theorems/931bd95c-7a5b-4c2b-bfca-e3737579018c
-- title:
--   Charge one scanner iteration and one multiplier call
-- statement:
--   Suppose a caller controller scans for s transitions until its designated call state, and a called controller then halts for the first time after u transitions. The combined finite controller performs the scanner segment and call in one run, returns to the designated resume state, and preserves the exact final tape contents and heads. Its exact clock is s+u+2, including both dispatch transitions.
-- source:
--   Composition of the exact caller-prefix simulation and the finite call-return controller theorem.

import Definitions.Def_BitDFT_CallReturn
set_option autoImplicit false
open IntMul BitDFT.MachineSequence BitDFT.CallReturn

theorem BitDFT.CallReturn.call_segment_run {M : MultitapeTM} (P Q : Controller M)
    (call resume : P.K) (hcall : call ≠ P.exit)
    (c : P.machine.Cfg) (s : ℕ) (cCall : P.machine.Cfg)
    (hp : P.machine.step^[s] c = cCall)
    (hbeforeP : ∀ r < s, (P.machine.step^[r] c).state ≠ call)
    (hcCall : cCall.state = call)
    (u : ℕ) (d : Q.machine.Cfg)
    (hbeforeQ : ∀ r < u, (Q.machine.step^[r] (enterQ P Q call resume cCall)).state ≠ Q.exit)
    (hq : Q.machine.step^[u] (enterQ P Q call resume cCall) = d)
    (hhalt : d.state = Q.exit) :
    (machine P Q call resume hcall).step^[s+u+2] (fromP P Q call resume hcall c) =
      fromP P Q call resume hcall (returnP P Q call resume d) := by sorry
