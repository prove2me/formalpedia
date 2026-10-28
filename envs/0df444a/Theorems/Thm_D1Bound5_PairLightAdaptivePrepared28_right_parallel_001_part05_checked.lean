-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:55.076995+00:00
-- url     : https://prove2.me/theorems/68bbd52f-6f2d-4e0d-b139-fdb23defcb79
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 5
-- statement:
--   For prepared pair 28, right list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 142 through 153, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_001Part05.lean, lines 10-14, SHA-256 56409084a88b3e8b126613424a3ae6f7755ffef31959d2f331d99347d32ce259. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_001_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 142) (PairLightPrepared28.rightRows.drop 142) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
