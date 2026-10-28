-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_left_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared48.left_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:58.695884+00:00
-- url     : https://prove2.me/theorems/6845a9ee-a5ff-422b-b04e-c90a1cba91d7
-- title:
--   Selected-floor prefix certificate for prepared pair 48, left list, part 2
-- statement:
--   For prepared pair 48, left list, part 2, the selected-floor certificate succeeds for at most `35` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 8, and the sieve is `PairLightPrepared48.sieve`. Original heads 59 through 93; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft48_000Part02.lean, lines 7-11, SHA-256 dc0fd940c39861e16811fa590a814cb298c2bafd242da290fcc0ae5874180cdb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared48.left_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 35
      (leftCached000.drop 59) (leftRows000.drop 59) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared48
end
