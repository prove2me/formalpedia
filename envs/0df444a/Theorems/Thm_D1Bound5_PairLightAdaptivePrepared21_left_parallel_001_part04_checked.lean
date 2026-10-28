-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_parallel_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:03.391981+00:00
-- url     : https://prove2.me/theorems/3bf32cab-8a0d-49c9-86f0-a722659283f2
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list, part 4
-- statement:
--   For prepared pair 21, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 130 through 141, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft21_001Part04.lean, lines 10-14, SHA-256 3fb00b5b768a701d07598b70314be73b5cdd99d1b1b3c08852b8c1b4f9b0f5f9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_parallel_001_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 130) (PairLightPrepared21.leftRows.drop 130) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
