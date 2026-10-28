-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared38.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:38.104995+00:00
-- url     : https://prove2.me/theorems/688629a3-a817-4e27-8ae3-ed5f17cbc989
-- title:
--   Selected-floor prefix certificate for prepared pair 38, left list
-- statement:
--   For prepared pair 38, left list, the selected-floor certificate succeeds for at most `280` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared38.sieve`. Heads 0 through 279; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft38_000.lean, lines 12-36, SHA-256 948fc0e8777c533b3cc9a53b199fa64db7d011df7f239a7588c18d89705b6afa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared38.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 280
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared38
end
