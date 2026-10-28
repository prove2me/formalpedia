-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_001_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:37:07.880531+00:00
-- url     : https://prove2.me/theorems/9b44de02-ae51-414e-b701-e47e187f59b9
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list
-- statement:
--   For prepared pair 19, right list, the selected-floor certificate succeeds for at most `147` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight19Prefix001.lean, lines 14-55, SHA-256 a3b22bdeef08666b3ea091942081a958db504874027898106c5128cc984bb11e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_direct_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 147
      (PairLightPrepared19.rightCached.drop 101) (PairLightPrepared19.rightRows.drop 101) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared19
end
