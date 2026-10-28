-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_signatures_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:38:13.45099+00:00
-- url     : https://prove2.me/theorems/f318b62b-f7f0-41c6-abd5-4b210ac8c96a
-- title:
--   Pair Light Adaptive Prepared39 — right signatures checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared39.right_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation39.lean, lines 20-23, SHA-256 2da6a639b1dc8bd636bc08e32ed3296fb07550fb8005b2c2cd6d418cab09cbd5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_signatures_checked :
    (PairLightPrepared39.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared39.sieve x.1)) = true := by sorry


end D1Bound5.PairLightAdaptivePrepared39
end
