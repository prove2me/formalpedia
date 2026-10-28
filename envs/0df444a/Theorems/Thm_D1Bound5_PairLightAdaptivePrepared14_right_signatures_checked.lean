-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_signatures_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:54:03.396852+00:00
-- url     : https://prove2.me/theorems/e72f3005-1352-405c-b859-233f44294662
-- title:
--   Pair Light Adaptive Prepared14 — right signatures checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared14.right_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation14.lean, lines 20-23, SHA-256 88acc11635f88ecf148966471161b05f271aff634a15dd0acdb1423630d28286. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_signatures_checked :
    (PairLightPrepared14.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared14.sieve x.1)) = true := by sorry


end D1Bound5.PairLightAdaptivePrepared14
end
