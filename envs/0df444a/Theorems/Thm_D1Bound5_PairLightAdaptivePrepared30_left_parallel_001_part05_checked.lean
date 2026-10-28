-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:54.910074+00:00
-- url     : https://prove2.me/theorems/542b8e3d-6041-4c3a-a786-158927ed2b07
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 5
-- statement:
--   For prepared pair 30, left list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 151 through 162, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_001Part05.lean, lines 10-14, SHA-256 cee1d0d827f0a6ea4a61f408977eafc8a58ebb347e32c810ecb9ae66d42cdb03. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 151) (PairLightPrepared30.leftRows.drop 151) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
