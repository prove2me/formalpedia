-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_000_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.right_prefix_000_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:53.527723+00:00
-- url     : https://prove2.me/theorems/487db8cb-4dd9-4f14-9443-c8b845d233ae
-- title:
--   Selected-floor prefix certificate for prepared pair 5, right list, part 8
-- statement:
--   For prepared pair 5, right list, part 8, the selected-floor certificate succeeds for at most `10` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 96 through 105, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight5_000Part08.lean, lines 11-16, SHA-256 cf75f50ea915c6fd6518645471338c69b50966d5ee978bbe63184e77d901f245. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.right_prefix_000_part08_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 10
      (PairLightPrepared5.rightCached.drop 96)
      (PairLightPrepared5.rightRows.drop 96) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
