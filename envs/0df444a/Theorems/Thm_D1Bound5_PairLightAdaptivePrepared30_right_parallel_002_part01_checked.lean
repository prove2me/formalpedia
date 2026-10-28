-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:25.784657+00:00
-- url     : https://prove2.me/theorems/0e2f22d7-a58d-48e8-8acd-fe2c1545730e
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 1
-- statement:
--   For prepared pair 30, right list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 226 through 237, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_002Part01.lean, lines 10-14, SHA-256 eec9606594da482681247bf9adf8a8b177bc446c1e80a7141b3a7ef1d3a898b2. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 226) (PairLightPrepared30.rightRows.drop 226) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
