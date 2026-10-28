-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_002_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_002_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:18.892616+00:00
-- url     : https://prove2.me/theorems/e2aecae7-7a6f-4547-b32f-b097888f986c
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 6
-- statement:
--   For prepared pair 28, left list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 256 through 267, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_002Part06.lean, lines 10-14, SHA-256 0771e60e14676b1705c2487fa79af41a03227d90bde6e3ed6f49efacb3995942. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_002_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 256) (PairLightPrepared28.leftRows.drop 256) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
