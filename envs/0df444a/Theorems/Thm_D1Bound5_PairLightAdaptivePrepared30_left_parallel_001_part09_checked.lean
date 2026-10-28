-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_001_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:00.230969+00:00
-- url     : https://prove2.me/theorems/6cd2b69f-3a29-401e-a3c1-46f3faf59675
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 9
-- statement:
--   For prepared pair 30, left list, part 9, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 199 through 210, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_001Part09.lean, lines 10-14, SHA-256 f576d165e53a725cf43aa880f45b6e91f81b9c206ea10ee265f3b834c635179d. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part09_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 199) (PairLightPrepared30.leftRows.drop 199) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
