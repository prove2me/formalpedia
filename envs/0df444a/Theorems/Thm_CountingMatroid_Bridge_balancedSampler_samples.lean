-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_balancedSampler_samples
-- name    : CountingMatroid.Bridge.balancedSampler_samples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T03:59:50.261991+00:00
-- url     : https://prove2.me/theorems/238da313-536c-41b4-9419-7a7d91903ba8
-- title:
--   Exact positions, output stack, and cost of finite-bit sampling
-- statement:
--   For every K and every infinite Boolean tape, the fixed sampler finishes after 3K+1 instructions. It stores exactly the K bits at positions 3i+1, in reverse order, leaves its input stack intact, and uses exactly 3K+1 bit operations. The positions are fixed by K and the index, independent of the sampled values.
-- source:
--   Lean 4.33.1 finite-randomness machine contribution to the existing counting-matroid mission; uses the local CommonBasesFPRAS instruction model and no Arlib definitions.

import Definitions.Def_CountingMatroidBridgeBalancedSampler
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem CountingMatroid.Bridge.balancedSampler_samples {n : ℕ}
    (O : OAI.CommonBasesFPRAS.IndependenceOracle n)
    (c : OAI.CommonBasesFPRAS.MachineConfig 2 4)
    (bits : ℕ → Bool) (K : ℕ) :
    let out := OAI.CommonBasesFPRAS.execution CountingMatroid.Bridge.balancedSampler O
      (CountingMatroid.Bridge.samplingConfig c bits K 0) bits (3 * K + 1)
    out.control = 4 ∧ out.output = none ∧ out.registers 8 = [] ∧
    out.registers 9 =
      (List.ofFn (fun i : Fin K => bits ((CountingMatroid.Bridge.samplingPositions K i).val))).reverse ++
        c.registers 9 ∧
    out.bitOperations = c.bitOperations + (3 * K + 1)
  := by
  sorry
