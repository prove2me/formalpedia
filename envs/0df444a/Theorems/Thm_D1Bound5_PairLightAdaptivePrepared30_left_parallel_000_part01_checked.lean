-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:31:36.001783+00:00
-- url     : https://prove2.me/theorems/b44e836b-f9a6-465a-882f-a528c9a9f337
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 1
-- statement:
--   For prepared pair 30, left list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 12 through 23, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_000Part01.lean, lines 10-14, SHA-256 c18963ac5cb07f2b79a6f0b566d2c02d8d2ef695fe7acefdeb65afba0aa977ff. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 12) (PairLightPrepared30.leftRows.drop 12) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
