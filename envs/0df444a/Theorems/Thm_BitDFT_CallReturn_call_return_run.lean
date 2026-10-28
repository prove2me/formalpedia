-- Prove2me | Theorems.Thm_BitDFT_CallReturn_call_return_run
-- name    : BitDFT.CallReturn.call_return_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T22:42:02.553717+00:00
-- url     : https://prove2.me/theorems/bd68cb5c-d8b4-4a2c-bfc8-20684c0e6623
-- title:
--   Run a child machine and return to the caller with exact tapes
-- statement:
--   Let P be a finite caller controller with a designated call state distinct from its halt state, and let Q be a called controller over the same tape alphabet and layout. If Q first reaches its halt state after u transitions, then the combined controller returns to P’s designated resume state after exactly u+2 transitions. The two additional transitions dispatch into Q and return from Q; all tape contents and head positions are preserved at both boundaries.
-- source:
--   A direct finite-state sum construction with exact transition-by-transition simulation of the called controller before its first halt, followed by a stationary return transition.

import Definitions.Def_BitDFT_CallReturn
set_option autoImplicit false
open IntMul BitDFT.MachineSequence BitDFT.CallReturn

theorem BitDFT.CallReturn.call_return_run {M : MultitapeTM} (P Q : Controller M)
    (call resume : P.K) (hcall : call ≠ P.exit)
    (c : P.machine.Cfg) (hc : c.state = call)
    (u : ℕ) (d : Q.machine.Cfg)
    (hbefore : ∀ s < u, (Q.machine.step^[s] (enterQ P Q call resume c)).state ≠ Q.exit)
    (hrun : Q.machine.step^[u] (enterQ P Q call resume c) = d)
    (hhalt : d.state = Q.exit) :
    (machine P Q call resume hcall).step^[u+2] (fromP P Q call resume hcall c) =
      fromP P Q call resume hcall (returnP P Q call resume d) := by sorry
