-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:31.867811+00:00
-- url     : https://prove2.me/theorems/b6b0272a-5746-499c-be21-f45d093b147f
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 0
-- statement:
--   For prepared pair 30, right list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 92 through 103, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_001Part00.lean, lines 10-14, SHA-256 f4e3179c2fed027033a15419452e6068dc42bb8dca1c7ffaee195761f3dd31fa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 92) (PairLightPrepared30.rightRows.drop 92) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
