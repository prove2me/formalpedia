-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_parallel_002_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_parallel_002_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:56.554987+00:00
-- url     : https://prove2.me/theorems/6d8a9054-55db-44c8-9db6-738b44e3e2f7
-- title:
--   Selected-floor prefix certificate for prepared pair 21, right list, part 10
-- statement:
--   For prepared pair 21, right list, part 10, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 304 through 315, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight21_002Part10.lean, lines 10-14, SHA-256 3872eb0420fecd11f99eab208b943167e68706d048c54d37857e40a1fc1ecb9f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_parallel_002_part10_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.rightCached.drop 304) (PairLightPrepared21.rightRows.drop 304) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
