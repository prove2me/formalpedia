-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:14.27491+00:00
-- url     : https://prove2.me/theorems/a51326b1-f917-4dbc-8bf5-285cdcf5eeb1
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 2
-- statement:
--   For prepared pair 36, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 191 through 202, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_002Part02.lean, lines 10-14, SHA-256 126c766f4ac6becfba1e898ddd2a695a82068f9a14f9468e0c03c95aa8088c75. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_002_part02_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 191) (PairLightPrepared36.rightRows.drop 191) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
