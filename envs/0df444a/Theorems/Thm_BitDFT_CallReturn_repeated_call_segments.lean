-- Prove2me | Theorems.Thm_BitDFT_CallReturn_repeated_call_segments
-- name    : BitDFT.CallReturn.repeated_call_segments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T23:00:01.58752+00:00
-- url     : https://prove2.me/theorems/906f4127-5c3b-4c8d-9bad-fa3ac9c85529
-- title:
--   Exact total clock for a finite sequence of scanner and call stages
-- statement:
--   Consider one caller controller that repeatedly scans from a resume configuration to a designated call state, invokes the same child controller, and resumes with the child's final tape frame. For stage i, let the caller scan take s_i transitions and let the child take u_i transitions. If each stage begins at the preceding stage's returned configuration, then after n stages the combined controller reaches the nth boundary configuration in exactly the sum of the stage clocks:
--   \[\sum_{i<n}(s_i+u_i+2).\]
--   The two extra transitions per stage are the stationary dispatch into the child and return to the caller. This theorem isolates the exact machine-time accounting required by a repeated coordinate-scaling loop.
-- source:
--   Composition of the accepted exact scanner-call-return theorem with the accepted finite-segment iterate theorem; supports the repeated scalar multiplication loop in the rescaling machine.

import Definitions.Def_BitDFT_CallReturn
import Theorems.Thm_BitDFT_CallReturn_call_segment_run
import Theorems.Thm_BitDFT_MachineSequence_iterate_segments
set_option autoImplicit false
open IntMul BitDFT.MachineSequence BitDFT.CallReturn

theorem BitDFT.CallReturn.repeated_call_segments {M : MultitapeTM} (P Q : Controller M)
    (call resume : P.K) (hcall : call ≠ P.exit)
    (cfg : ℕ → P.machine.Cfg) (callCfg : ℕ → P.machine.Cfg)
    (result : ℕ → Q.machine.Cfg) (s u : ℕ → ℕ)
    (hscan : ∀ i, P.machine.step^[s i] (cfg i) = callCfg i)
    (hbeforeP : ∀ i r, r < s i → (P.machine.step^[r] (cfg i)).state ≠ call)
    (hcallState : ∀ i, (callCfg i).state = call)
    (hbeforeQ : ∀ i r, r < u i →
      (Q.machine.step^[r] (enterQ P Q call resume (callCfg i))).state ≠ Q.exit)
    (hchild : ∀ i, Q.machine.step^[u i] (enterQ P Q call resume (callCfg i)) = result i)
    (hhalt : ∀ i, (result i).state = Q.exit)
    (hnext : ∀ i, returnP P Q call resume (result i) = cfg (i + 1))
    (n : ℕ) :
    (machine P Q call resume hcall).step^[∑ i ∈ Finset.range n, (s i + u i + 2)]
      (fromP P Q call resume hcall (cfg 0)) =
      fromP P Q call resume hcall (cfg n) := by sorry
