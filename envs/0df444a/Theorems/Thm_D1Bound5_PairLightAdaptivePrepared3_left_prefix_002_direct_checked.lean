-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_002_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.left_prefix_002_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:39:18.583896+00:00
-- url     : https://prove2.me/theorems/bb669974-4eaa-49f6-9737-0db8fd8318b0
-- title:
--   Selected-floor prefix certificate for prepared pair 3, left list
-- statement:
--   For prepared pair 3, left list, the selected-floor certificate succeeds for at most `102` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft3Prefix002.lean, lines 12-41, SHA-256 781bfa3e3c8f9905c25638218c600d1578c8fcdaa7e407095dff01d70fb89e22. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared3.left_prefix_002_direct_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 102
      (PairLightPrepared3.leftCached.drop 311) (PairLightPrepared3.leftRows.drop 311) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared3
end
