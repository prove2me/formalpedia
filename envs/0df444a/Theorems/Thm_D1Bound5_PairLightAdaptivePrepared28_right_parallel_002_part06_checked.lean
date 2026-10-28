-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_002_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_002_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:08.571597+00:00
-- url     : https://prove2.me/theorems/b19441d5-c0db-4df4-a061-9abea67797d3
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 6
-- statement:
--   For prepared pair 28, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 256 through 267, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_002Part06.lean, lines 10-14, SHA-256 8d3ce59c6e3921390e3243916ac7c13c3cb9e408a0a14ff4a32b4f4dc0d4ddc5. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_002_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 256) (PairLightPrepared28.rightRows.drop 256) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
