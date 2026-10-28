-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_001_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_001_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:30.348564+00:00
-- url     : https://prove2.me/theorems/cb888b00-88af-4cb0-ba24-4196d9c6b00b
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 6
-- statement:
--   For prepared pair 28, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 154 through 165, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_001Part06.lean, lines 10-14, SHA-256 5e95dadbee12b238d7570ad0e8cca2262954ae652c565cd6473e0ee1fd4bbcc6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_001_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 154) (PairLightPrepared28.rightRows.drop 154) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
