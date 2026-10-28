-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_signatures_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:06:52.962755+00:00
-- url     : https://prove2.me/theorems/24a6fb9f-13e8-4987-812f-b7306c5e06d0
-- title:
--   Pair Light Adaptive Prepared21 — left signatures checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared21.left_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation21.lean, lines 11-14, SHA-256 8926dc2071f521b1b3c2b556d7d3f2e7e770b9cdabead72da2dd9587d4c5a46f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_signatures_checked :
    (PairLightPrepared21.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared21.sieve x.1)) = true := by sorry






end D1Bound5.PairLightAdaptivePrepared21
end
