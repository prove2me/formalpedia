-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:27.289967+00:00
-- url     : https://prove2.me/theorems/7370ad5d-c529-4610-998d-235ecc9e147b
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list
-- statement:
--   For prepared pair 30, left list, the selected-floor certificate succeeds for at most `270` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft30_002.lean, lines 31-168, SHA-256 c98186f0dedd2328d92e508ce97c22f517b3ad916c0ea942eef446c4f7ff9d29. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData30_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 270
      leftCached002 leftRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
