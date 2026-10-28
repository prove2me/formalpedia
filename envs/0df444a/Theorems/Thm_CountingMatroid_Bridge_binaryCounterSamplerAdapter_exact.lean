-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_binaryCounterSamplerAdapter_exact
-- name    : CountingMatroid.Bridge.binaryCounterSamplerAdapter_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T19:54:20.479485+00:00
-- url     : https://prove2.me/theorems/ffd4615e-407e-4191-b5b1-f558deee4052
-- title:
--   The finite sampler prefix hands off the exact sample
-- statement:
--   For every fixed continuation and K ≤ H, the counter-and-sampler prefix from the parameter initializer reaches that continuation with the exact K tape bits, read in the source estimator’s order from distinct positions in a polynomially long finite tape. The prefix makes no oracle calls and its bit-operation count equals its deterministic instruction count.
-- source:
--   This theorem is the already verified local sampler-handoff result. Its counter loop is deterministic; the balanced sampler uses fixed three-step cycles, so the random-bit locations depend only on K and are distinct. The proved finite-tape embedding transfers the exact ordered sample and the prefix-cost invariant.

import Mathlib
import Definitions.Def_CountingMatroidBridgeBinarySampler

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS CountingMatroid.Bridge

theorem CountingMatroid.Bridge.binaryCounterSamplerAdapter_exact
    {s n r K H : ℕ} (P : Program 2 s) (O : IndependenceOracle n)
    (tape : Fin (26 * (H + 1) ^ 2) → Bool) (hK : K ≤ H)
    (ε δ : ℚ) :
    let c := initialConfig 2 (s + 15) n r ε δ
    let bits := fun t => finiteBits tape t
    let counterSteps := binaryCounterCountdownSteps K K.bits
    let prefixLength := counterSteps + (3 * K + 1)
    let sampled := execution (binaryCounterThenProgram P) O
      (binarySamplerInput c K) bits prefixLength
    sampled.control.val = 15 ∧ sampled.output = none ∧
      sampled.registers 9 = List.ofFn (fun i : Fin K =>
        tape (binaryCounterSamplingPositionsPolynomialReversed K H hK i)) ∧
      sampled.oracleCalls = 0 ∧ sampled.bitOperations = prefixLength := by
  sorry
