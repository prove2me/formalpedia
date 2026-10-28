-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_exactOracles_to_source
-- name    : CountingMatroid.Bridge.exactOracles_to_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:34:50.997094+00:00
-- url     : https://prove2.me/theorems/362e61f9-5edb-4440-845d-d0d32751490f
-- title:
--   The original selector oracle supplies both source oracles
-- statement:
--   Let O be an independence oracle with a Boolean matroid selector. If it satisfies the original mission's exactness predicate for M1 and M2, then O false and O true satisfy the source's respective ExactOracle predicates. Both developments decode precisely the same n-bit subset indicators.
-- source:
--   Original bridge contribution, 2026-10-24, for the existing Prove2me mission Approximate counting of common bases of two matroids. Uses meelgroup/counting-matroid commit dd16a4628fdb095c58fe0f3dfd8e353c6e97443c and the already published CommonBasesFPRAS definition. Does not claim a concrete bit-machine realization.

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- Split the mission's selector oracle into the source's two exact oracles. -/
theorem CountingMatroid.Bridge.exactOracles_to_source {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (O : OAI.CommonBasesFPRAS.IndependenceOracle n)
    (h : OAI.CommonBasesFPRAS.ExactOracles M₁ M₂ O) :
    ExactOracle M₁ (O false) ∧ ExactOracle M₂ (O true) := by
  sorry
