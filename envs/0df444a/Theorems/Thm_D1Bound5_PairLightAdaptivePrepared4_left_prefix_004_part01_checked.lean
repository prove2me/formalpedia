-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_004_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_004_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:18.031011+00:00
-- url     : https://prove2.me/theorems/6389b93b-89e9-497c-b404-7889832a2a64
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 1
-- statement:
--   For prepared pair 4, left list, part 1, the selected-floor certificate succeeds for at most `45` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 441 through 485, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_004Part01.lean, lines 11-16, SHA-256 a07bca9ce4ea5f68ec53c58c7d7d5e7742b5e7e8ef14e734e1ebc11b24b83b3b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_004_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 45
      (PairLightPrepared4.leftCached.drop 441)
      (PairLightPrepared4.leftRows.drop 441) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
