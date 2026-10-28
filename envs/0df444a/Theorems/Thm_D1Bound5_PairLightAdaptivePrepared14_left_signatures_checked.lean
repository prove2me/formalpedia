-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_signatures_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:34:55.258395+00:00
-- url     : https://prove2.me/theorems/89262ff2-3b20-43e3-9863-91c1a484d496
-- title:
--   Pair Light Adaptive Prepared14 — left signatures checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared14.left_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation14.lean, lines 11-14, SHA-256 88acc11635f88ecf148966471161b05f271aff634a15dd0acdb1423630d28286. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_signatures_checked :
    (PairLightPrepared14.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared14.sieve x.1)) = true := by sorry






end D1Bound5.PairLightAdaptivePrepared14
end
