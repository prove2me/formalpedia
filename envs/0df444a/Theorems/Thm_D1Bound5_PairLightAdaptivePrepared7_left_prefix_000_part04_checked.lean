-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:51:21.013986+00:00
-- url     : https://prove2.me/theorems/240b02f5-cad4-494f-b042-0aacc87291cb
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list, part 4
-- statement:
--   For prepared pair 7, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 48 through 59, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft7_000Part04.lean, lines 11-16, SHA-256 0202042c7b04f0a9e33d407fb47e4facb0f909fab6a2989f62cd23886137d8bb. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 12
      (PairLightPrepared7.leftCached.drop 48)
      (PairLightPrepared7.leftRows.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
