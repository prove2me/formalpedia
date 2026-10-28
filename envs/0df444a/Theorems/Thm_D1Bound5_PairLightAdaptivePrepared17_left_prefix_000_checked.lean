-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:42:30.222029+00:00
-- url     : https://prove2.me/theorems/88c54b6a-5268-453f-8f74-070fa50b650a
-- title:
--   Selected-floor prefix certificate for prepared pair 17, left list
-- statement:
--   For prepared pair 17, left list, the selected-floor certificate succeeds for at most `137` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Heads 0 through 136; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft17_000.lean, lines 13-43, SHA-256 e9703d26d330bd5296481d9f2039aeaa84c48f99ee15b5e099ab4da8d6ab3742. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 137
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
