-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_appendProgram_execution_decode
-- name    : CountingMatroid.Bridge.appendProgram_execution_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T04:28:45.403983+00:00
-- url     : https://prove2.me/theorems/f0a32bb7-eb8a-48a6-8786-f415496fcee7
-- title:
--   Execution after a fixed sampler prefix
-- statement:
--   Suppose the combined program has reached its continuation state after the finite-bit sampling prefix. For every later tape and every number of steps, decoding its configuration gives exactly the configuration obtained by running the supplied estimator program for that many steps from its start state. Registers, output, oracle-call count, and bit-operation count are preserved.
-- source:
--   Lean 4.33.1 machine-composition contribution to the existing counting-matroid mission; no Arlib dependency.

import Definitions.Def_CountingMatroidBridgeProgramAppend
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem CountingMatroid.Bridge.appendProgram_execution_decode {s n : ℕ}
    (P : OAI.CommonBasesFPRAS.Program 2 s)
    (O : OAI.CommonBasesFPRAS.IndependenceOracle n)
    (c : OAI.CommonBasesFPRAS.MachineConfig 2 (s + 5))
    (bits : ℕ → Bool) (t : ℕ)
    (hcontrol : c.control.val = 4) :
    CountingMatroid.Bridge.decodeProgramConfig
      (OAI.CommonBasesFPRAS.execution (CountingMatroid.Bridge.sampleThenProgram P)
        O c bits t) =
    OAI.CommonBasesFPRAS.execution P O
        (CountingMatroid.Bridge.programStartConfig c) bits t := by
  sorry
