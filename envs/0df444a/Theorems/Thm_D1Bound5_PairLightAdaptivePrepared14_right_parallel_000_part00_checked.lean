-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:53.742853+00:00
-- url     : https://prove2.me/theorems/a6f4e6ea-f6ec-4e23-ad34-be3724b9509a
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 0
-- statement:
--   For prepared pair 14, right list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 0 through 11, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_000Part00.lean, lines 10-14, SHA-256 cd79fb02702daf687ef27f77d46e95835ce4efab71ebdaafc33ede17bfd3d13e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_000_part00_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 0) (PairLightPrepared14.rightRows.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
