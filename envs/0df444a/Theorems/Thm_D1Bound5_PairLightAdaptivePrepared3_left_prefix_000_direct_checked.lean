-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_000_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:40:05.674551+00:00
-- url     : https://prove2.me/theorems/6c3f1ca2-19fa-476d-b198-3dfe361778a0
-- title:
--   Selected-floor prefix certificate for prepared pair 3, left list
-- statement:
--   For prepared pair 3, left list, the selected-floor certificate succeeds for at most `112` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft3Prefix000.lean, lines 17-76, SHA-256 891845ebcac757938584206175c46c86db9c865c65350bea214d64f38fc50dcf. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_direct_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 112
      (PairLightPrepared3.leftCached.drop 0) (PairLightPrepared3.leftRows.drop 0) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared3
end
