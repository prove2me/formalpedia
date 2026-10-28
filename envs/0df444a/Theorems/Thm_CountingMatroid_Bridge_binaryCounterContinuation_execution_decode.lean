-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_binaryCounterContinuation_execution_decode
-- name    : CountingMatroid.Bridge.binaryCounterContinuation_execution_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T20:01:25.354485+00:00
-- url     : https://prove2.me/theorems/af24d163-ad83-4875-bc2a-908d9847e798
-- title:
--   The sampler prefix simulates an arbitrary continuation
-- statement:
--   After the deterministic counter and sampling prefix, the combined program exactly simulates every subsequent step of an arbitrary continuation program. The simulation preserves the registers, oracle interactions, output, and cost counters; its only change is the fixed offset in the random-bit stream.
-- source:
--   The combined program shifts every continuation instruction by the fixed prefix offset. A configuration decoder subtracts that offset, and induction on the execution length proves exact step-by-step correspondence, including oracle instructions.

import Definitions.Def_CountingMatroidBridgeBinarySampler

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS CountingMatroid.Bridge

theorem CountingMatroid.Bridge.binaryCounterContinuation_execution_decode {s n K : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n)
    (c : MachineConfig 2 (s + 15)) (bits : ℕ → Bool)
    (hcontrol : c.control = (⟨0, by omega⟩ : Fin (s + 15 + 1)))
    (houtput : c.output = none) (hscratch : c.registers 6 = [])
    (hcounter : c.registers 8 = []) (t : ℕ) :
    let input := binarySamplerInput c K
    let totalPrefix := binaryCounterCountdownSteps K K.bits + (3 * K + 1)
    let sampled := execution (binaryCounterThenProgram P) O input bits totalPrefix
    binaryCounterDecodeConfig
        (execution (binaryCounterThenProgram P) O input bits (totalPrefix + t)) =
      execution P O (binaryCounterProgramStartConfig sampled)
        (fun j => bits (totalPrefix + j)) t := by
  sorry
