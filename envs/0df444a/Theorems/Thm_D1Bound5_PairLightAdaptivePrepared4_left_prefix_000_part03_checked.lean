-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:21:35.175574+00:00
-- url     : https://prove2.me/theorems/afbfdf67-c479-4eab-a3ce-a1f6fdbd92af
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 3
-- statement:
--   For prepared pair 4, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 34 through 45, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_000Part03.lean, lines 11-16, SHA-256 be0cc18d46d92e40498c2b5eea898235b13f695480286d183a4591fea74f6cff. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 12
      (PairLightPrepared4.leftCached.drop 34)
      (PairLightPrepared4.leftRows.drop 34) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
