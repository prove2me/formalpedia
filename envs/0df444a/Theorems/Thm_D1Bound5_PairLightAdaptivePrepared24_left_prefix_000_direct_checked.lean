-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_000_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_000_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:39:23.502427+00:00
-- url     : https://prove2.me/theorems/035c97dc-9885-4c67-bf90-13e822fafe2c
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list
-- statement:
--   For prepared pair 24, left list, the selected-floor certificate succeeds for at most `101` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft24Prefix000.lean, lines 16-69, SHA-256 317844a97a078b136ddc614f6c11c8afeed6f2933f8e602e25494457635e7519. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_000_direct_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 101
      (PairLightPrepared24.leftCached.drop 0) (PairLightPrepared24.leftRows.drop 0) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared24
end
