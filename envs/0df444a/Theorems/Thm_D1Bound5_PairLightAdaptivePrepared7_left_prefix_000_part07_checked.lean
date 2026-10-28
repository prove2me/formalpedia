-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_000_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_000_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:40.311985+00:00
-- url     : https://prove2.me/theorems/350a4a33-67d9-49fb-9fe3-0816804c34af
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list, part 7
-- statement:
--   For prepared pair 7, left list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 84 through 95, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft7_000Part07.lean, lines 11-16, SHA-256 d84e0e354b062831d39242b53c60c83825fd8bb0a1bbe28bf8a11603761b265e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_000_part07_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 12
      (PairLightPrepared7.leftCached.drop 84)
      (PairLightPrepared7.leftRows.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
