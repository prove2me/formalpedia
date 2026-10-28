-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:49.304068+00:00
-- url     : https://prove2.me/theorems/6ebb0a74-affc-4913-8ce1-161c878732c3
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list, part 4
-- statement:
--   For prepared pair 24, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 48 through 59, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft24_000Part04.lean, lines 11-16, SHA-256 fdc30f97571c21cd611403a9bc87af4025dd06f1687642c57d09b1b43676b819. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 12
      (PairLightPrepared24.leftCached.drop 48)
      (PairLightPrepared24.leftRows.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
