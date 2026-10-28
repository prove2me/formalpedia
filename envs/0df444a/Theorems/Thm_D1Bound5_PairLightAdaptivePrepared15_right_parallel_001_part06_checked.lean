-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:56.139198+00:00
-- url     : https://prove2.me/theorems/f30c3b3e-7307-45da-aa38-cf4509eb43d0
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 6
-- statement:
--   For prepared pair 15, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 164 through 175, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_001Part06.lean, lines 10-14, SHA-256 9629a264fc2ff229b57b3e4f3cb8a6f420480260c89d9899ff9d4540bebf4104. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part06_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 164) (PairLightPrepared15.rightRows.drop 164) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
