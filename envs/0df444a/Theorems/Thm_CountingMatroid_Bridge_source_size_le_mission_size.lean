-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_source_size_le_mission_size
-- name    : CountingMatroid.Bridge.source_size_le_mission_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:35:40.808461+00:00
-- url     : https://prove2.me/theorems/fa6a4cb5-6d0c-4712-944f-e63917aad108
-- title:
--   The source size is bounded by the original mission size
-- statement:
--   For every n, r and valid accuracy/confidence input, the source polynomial-size base is at most six times the original mission's base. The latter is one plus n, the binary input length defined in CommonBasesFPRAS, the ceiling of reciprocal accuracy, and the ceiling binary logarithm of the ceiling of reciprocal confidence. This comparison requires no matroid or oracle promise.
-- source:
--   Original bridge contribution, 2026-10-24, for the existing Prove2me mission Approximate counting of common bases of two matroids. Uses meelgroup/counting-matroid commit dd16a4628fdb095c58fe0f3dfd8e353c6e97443c and the already published CommonBasesFPRAS definition. Does not claim a concrete bit-machine realization.

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Bridge_binaryNatLength_le_bits_length_add_one

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- The imported source size is at most six times the base used by the
original mission's polynomial resource bound. No matroid promise is needed. -/
theorem CountingMatroid.Bridge.source_size_le_mission_size (n r : ℕ) (p : InputParams) :
    n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
      binaryNatLength (Nat.ceil p.δ⁻¹) + 1 ≤
    6 * (1 + n + OAI.CommonBasesFPRAS.inputLength n r p.ε p.δ +
      Nat.ceil p.ε⁻¹ + Nat.clog 2 (Nat.ceil p.δ⁻¹)) := by
  sorry
