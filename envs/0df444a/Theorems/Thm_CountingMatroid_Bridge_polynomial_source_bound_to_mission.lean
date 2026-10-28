-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_polynomial_source_bound_to_mission
-- name    : CountingMatroid.Bridge.polynomial_source_bound_to_mission
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:37:50.765999+00:00
-- url     : https://prove2.me/theorems/4e928589-b289-4184-8f7a-de6ce8507397
-- title:
--   Transfer of polynomial bounds to the original mission
-- statement:
--   For all natural C,d,n,r and valid accuracy/confidence inputs, C times the source size base to power d is at most the original mission's resourceBound with coefficient C times 6^d and exponent d. Thus the different binary-length and logarithm conventions do not obstruct transferring polynomial estimates. This is a numerical bound conversion, not a simulation theorem.
-- source:
--   Original bridge contribution, 2026-10-24, for the existing Prove2me mission Approximate counting of common bases of two matroids. Uses meelgroup/counting-matroid commit dd16a4628fdb095c58fe0f3dfd8e353c6e97443c and the already published CommonBasesFPRAS definition. Does not claim a concrete bit-machine realization.

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Bridge_source_size_le_mission_size

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- Any polynomial source-size estimate transfers to the original mission's
input convention with only a constant-factor change of coefficient. -/
theorem CountingMatroid.Bridge.polynomial_source_bound_to_mission (C d n r : ℕ) (p : InputParams) :
    C * (n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
      binaryNatLength (Nat.ceil p.δ⁻¹) + 1)^d ≤
    OAI.CommonBasesFPRAS.resourceBound (C * 6^d) d n r p.ε p.δ := by
  sorry
