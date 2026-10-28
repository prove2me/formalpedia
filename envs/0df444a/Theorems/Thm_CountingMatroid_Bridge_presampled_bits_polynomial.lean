-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_presampled_bits_polynomial
-- name    : CountingMatroid.Bridge.presampled_bits_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:31:15.014973+00:00
-- url     : https://prove2.me/theorems/b4db31b5-5cdb-4d46-870f-4194a0b8bb26
-- title:
--   The complete pre-sampled random tape has polynomial length
-- statement:
--   There exist uniform natural constants C and d such that, for every n, r and valid accuracy/confidence input, the repetition count times the prescribed block length is at most C X^d. Here X is one plus n, the source binary input length, the ceiling of reciprocal accuracy, and the binary length of the ceiling of reciprocal confidence. Thus even sampling all prescribed bits, including unused bits, needs only polynomially many coin draws. This does not yet bound the machine cost of generating, storing, or evaluating that tape.
-- source:
--   Original bridge contribution, 2026-10-24, for the existing Prove2me mission Approximate counting of common bases of two matroids. Uses meelgroup/counting-matroid commit dd16a4628fdb095c58fe0f3dfd8e353c6e97443c and the already published CommonBasesFPRAS definition. Does not claim a concrete bit-machine realization.

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Analysis_ScheduleValueEnvelope_schedule_value_envelope
import Theorems.Thm_CountingMatroid_Bridge_schedule_drawCalls_eq

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- Sampling every prescribed bit, including unused bits, costs polynomially
many coin draws in the source input-size parameter. This theorem concerns
the number of bits, not the implementation cost of the estimator. -/
theorem CountingMatroid.Bridge.presampled_bits_polynomial :
    ∃ C d : ℕ, ∀ (n r : ℕ) (p : InputParams),
      (Program.schedule n p).val.repetitions * blockLength n r p ≤
        C * (n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
          binaryNatLength (Nat.ceil p.δ⁻¹) + 1)^d := by
  sorry
