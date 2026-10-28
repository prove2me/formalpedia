-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:17.920203+00:00
-- url     : https://prove2.me/theorems/d48fe90a-de5e-4196-ae73-19c2aaecc500
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 3
-- statement:
--   For prepared pair 10, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 34 through 45, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_000Part03.lean, lines 11-16, SHA-256 bfe955d8d24b7b040e50b260dde8c1b8470df019b21809352d163fe7f1aae77e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 12
      (PairLightPrepared10.leftCached.drop 34)
      (PairLightPrepared10.leftRows.drop 34) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
