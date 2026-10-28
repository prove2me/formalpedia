-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_002_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:51.818349+00:00
-- url     : https://prove2.me/theorems/1c539f18-d834-4e78-9eb7-1051d2355a91
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 7
-- statement:
--   For prepared pair 30, left list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 296 through 307, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_002Part07.lean, lines 10-14, SHA-256 f73bd55b3797e96250b77a8e323878e71ed78135467e27dc499d1cec28391b64. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 296) (PairLightPrepared30.leftRows.drop 296) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
