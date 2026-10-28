-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_parallel_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:58.155282+00:00
-- url     : https://prove2.me/theorems/94f6d917-1833-440e-88c1-78e32f784fdb
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list, part 3
-- statement:
--   For prepared pair 21, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 118 through 129, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft21_001Part03.lean, lines 10-14, SHA-256 1bfd22f6dd36d5a31181de0680e22093306c43f9bef215dce162b47b0fc67030. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_parallel_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 118) (PairLightPrepared21.leftRows.drop 118) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
