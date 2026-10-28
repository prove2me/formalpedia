-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared20_right_signatures_checked
-- name    : D1Bound5.PairLightPrepared20.right_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:26:47.874861+00:00
-- url     : https://prove2.me/theorems/fbd83595-6406-4336-a5f3-c3e09b8269a6
-- title:
--   Pair Light Prepared20 — right signatures checked
-- statement:
--   Auxiliary result `PairLightPrepared20.right_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight20.lean, lines 13-15, SHA-256 58b6b5b1ae790cff7408d6ecfe0ed47e733d5d10e8ae38db09441ffcb0a6f1b5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_004

section
namespace D1Bound5.PairLightPrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightPrepared20.right_signatures_checked :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true := by sorry





end D1Bound5.PairLightPrepared20
end
