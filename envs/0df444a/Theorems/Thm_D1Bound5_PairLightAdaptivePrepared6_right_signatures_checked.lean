-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_signatures_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:31:24.887688+00:00
-- url     : https://prove2.me/theorems/bb90832f-48a9-46c8-a283-b762320df7fc
-- title:
--   Pair Light Adaptive Prepared6 — right signatures checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared6.right_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation6.lean, lines 20-23, SHA-256 28ec548a27c1621ae0a615dd43968304121b99bbb142ea55bc0b3cf0666d651c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_signatures_checked :
    (PairLightPrepared6.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared6.sieve x.1)) = true := by sorry


end D1Bound5.PairLightAdaptivePrepared6
end
