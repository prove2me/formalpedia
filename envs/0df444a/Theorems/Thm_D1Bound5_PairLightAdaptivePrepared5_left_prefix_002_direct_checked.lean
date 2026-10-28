-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_002_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.left_prefix_002_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:38:20.59599+00:00
-- url     : https://prove2.me/theorems/2a1cab74-0755-4257-965a-ace50afbc12d
-- title:
--   Selected-floor prefix certificate for prepared pair 5, left list
-- statement:
--   For prepared pair 5, left list, the selected-floor certificate succeeds for at most `162` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft5Prefix002.lean, lines 14-55, SHA-256 b88eb06123d1707eaf46be2984ad23eecf8f092fa2e04effe86b7d3bb37859f6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared5.left_prefix_002_direct_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 162
      (PairLightPrepared5.leftCached.drop 269) (PairLightPrepared5.leftRows.drop 269) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared5
end
