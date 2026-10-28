-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_004_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_004_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:30.083685+00:00
-- url     : https://prove2.me/theorems/3fbc9240-719f-48ea-9cfb-c464eb044dfe
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 1
-- statement:
--   For prepared pair 8, left list, part 1, the selected-floor certificate succeeds for at most `16` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 289 through 304, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_004Part01.lean, lines 11-16, SHA-256 86649e3d2ce220096e108cc162ff118c2f3ac9f18b764130938a27d56d1e78c9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_004_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 16
      (PairLightPrepared8.leftCached.drop 289)
      (PairLightPrepared8.leftRows.drop 289) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
