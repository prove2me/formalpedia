-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_003_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:22.314598+00:00
-- url     : https://prove2.me/theorems/a178db4c-a816-46ad-bdd4-b1ff4dd9005f
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 5
-- statement:
--   For prepared pair 28, left list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 395 through 406, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_003Part05.lean, lines 10-14, SHA-256 cd816279f12b0ddddb0b71df37e7674c66adf192338b3470fe89393113e85d59. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 395) (PairLightPrepared28.leftRows.drop 395) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
