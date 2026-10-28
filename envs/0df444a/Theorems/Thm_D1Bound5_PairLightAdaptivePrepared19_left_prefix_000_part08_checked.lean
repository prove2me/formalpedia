-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_prefix_000_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.left_prefix_000_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:34.786402+00:00
-- url     : https://prove2.me/theorems/d3628df1-8121-4cbd-afcc-9b44d6831728
-- title:
--   Selected-floor prefix certificate for prepared pair 19, left list, part 8
-- statement:
--   For prepared pair 19, left list, part 8, the selected-floor certificate succeeds for at most `5` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 96 through 100, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft19_000Part08.lean, lines 11-16, SHA-256 81843ef5db08e1fcc37969d67a62545c6b2a4c6d2b7316c36a6a5d924f247cdd. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.left_prefix_000_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 5
      (PairLightPrepared19.leftCached.drop 96)
      (PairLightPrepared19.leftRows.drop 96) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
