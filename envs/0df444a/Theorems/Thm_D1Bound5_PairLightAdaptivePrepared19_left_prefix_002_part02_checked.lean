-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_prefix_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.left_prefix_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:26.487722+00:00
-- url     : https://prove2.me/theorems/0b44c979-4077-4fad-9329-447436b6c9a4
-- title:
--   Selected-floor prefix certificate for prepared pair 19, left list, part 2
-- statement:
--   For prepared pair 19, left list, part 2, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 296 through 319, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft19_002Part02.lean, lines 11-16, SHA-256 b02b18e2ea7eefbd6aa897a200637fc7b0255639955c01a78688a032e0f5ab6c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.left_prefix_002_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.leftCached.drop 296)
      (PairLightPrepared19.leftRows.drop 296) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
