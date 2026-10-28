-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_000_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_000_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:07.076739+00:00
-- url     : https://prove2.me/theorems/6a83b55f-62ab-4eed-ae7e-50572833a790
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 7
-- statement:
--   For prepared pair 14, right list, part 7, the selected-floor certificate succeeds for at most `4` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 84 through 87, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_000Part07.lean, lines 10-14, SHA-256 d362cc3aeb3a70e127dcaaf23fa676871bf28465a5c698f4d121fa29ae45e0a3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_000_part07_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 4
      (PairLightPrepared14.rightCached.drop 84) (PairLightPrepared14.rightRows.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
