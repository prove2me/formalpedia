-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_signatures_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:07:23.92993+00:00
-- url     : https://prove2.me/theorems/0fe2f6f1-d9e9-4175-a489-f23918ee4071
-- title:
--   Pair Light Adaptive Prepared28 — right signatures checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared28.right_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation28.lean, lines 20-23, SHA-256 e1c9c8b67a795b78d7aba8a8cd799c6024a1e0dcb9f889d01da0535aa77c8f89. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_signatures_checked :
    (PairLightPrepared28.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared28.sieve x.1)) = true := by sorry


end D1Bound5.PairLightAdaptivePrepared28
end
