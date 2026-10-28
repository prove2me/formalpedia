-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_001_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.left_prefix_001_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:37:06.33725+00:00
-- url     : https://prove2.me/theorems/d56077d4-98fc-4aad-8955-5514cd1e90df
-- title:
--   Selected-floor prefix certificate for prepared pair 3, left list
-- statement:
--   For prepared pair 3, left list, the selected-floor certificate succeeds for at most `199` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft3Prefix001.lean, lines 16-69, SHA-256 7a1d03fe003c3cae8fc7f42dba04921bcc1bb4df9a4e54393cc62b953feffb7e. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared3.left_prefix_001_direct_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 199
      (PairLightPrepared3.leftCached.drop 112) (PairLightPrepared3.leftRows.drop 112) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared3
end
