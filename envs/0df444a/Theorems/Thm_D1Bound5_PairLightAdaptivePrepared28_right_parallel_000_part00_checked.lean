-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:43.294301+00:00
-- url     : https://prove2.me/theorems/15bb8c38-d9ab-4ba7-937e-04239a875b76
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 0
-- statement:
--   For prepared pair 28, right list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 0 through 11, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_000Part00.lean, lines 10-14, SHA-256 2ffead1a883575de9601cc1ba39cbfa6a0791438e3c9fdf8e41ba79e1a175eb6. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 0) (PairLightPrepared28.rightRows.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
