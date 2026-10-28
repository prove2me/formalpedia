-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_signatures_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:25:40.932209+00:00
-- url     : https://prove2.me/theorems/98a19c66-471a-412a-8ff0-099f65a70969
-- title:
--   Pair Light Adaptive Prepared36 — left signatures checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared36.left_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation36.lean, lines 11-14, SHA-256 240871f1b54ab24ee38331ca1a4d007af0d72d92a6af2f35022eabf55b7ed9fa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_signatures_checked :
    (PairLightPrepared36.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared36.sieve x.1)) = true := by sorry






end D1Bound5.PairLightAdaptivePrepared36
end
