-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_003_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_003_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:56.902772+00:00
-- url     : https://prove2.me/theorems/ee22038b-dbef-4614-b2bf-655d3a05c253
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 5
-- statement:
--   For prepared pair 14, right list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 477 through 488, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_003Part05.lean, lines 10-14, SHA-256 383f37682931c759238b852ab2e4cf6a7378899923829420914466dc581d89bf. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_003_part05_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 477) (PairLightPrepared14.rightRows.drop 477) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
