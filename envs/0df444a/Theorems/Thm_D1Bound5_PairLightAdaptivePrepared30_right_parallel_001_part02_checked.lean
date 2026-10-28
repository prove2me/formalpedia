-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:48.296613+00:00
-- url     : https://prove2.me/theorems/21a02319-5aa0-443c-b62b-c5f67268038b
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 2
-- statement:
--   For prepared pair 30, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 116 through 127, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_001Part02.lean, lines 10-14, SHA-256 d95a782294d1399c022a6bf073add1b39d7da709620e66d3e0591f3a2a51f21a. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 116) (PairLightPrepared30.rightRows.drop 116) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
