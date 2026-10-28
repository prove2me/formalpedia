-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_001_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_001_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:43.557294+00:00
-- url     : https://prove2.me/theorems/4083137f-18df-47eb-b9f3-dfafa35c993a
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list
-- statement:
--   For prepared pair 24, left list, the selected-floor certificate succeeds for at most `147` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft24Prefix001.lean, lines 14-55, SHA-256 97df0d685f8b336421eb11b5a9ba1e6b75d952dc7ca029422948d88703eae0f9. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_001_direct_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 147
      (PairLightPrepared24.leftCached.drop 101) (PairLightPrepared24.leftRows.drop 101) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared24
end
