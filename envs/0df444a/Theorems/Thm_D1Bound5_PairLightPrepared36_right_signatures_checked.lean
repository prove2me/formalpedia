-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared36_right_signatures_checked
-- name    : D1Bound5.PairLightPrepared36.right_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:18:13.03923+00:00
-- url     : https://prove2.me/theorems/7a8866ff-ee49-436d-92b5-a380981a0ff5
-- title:
--   Pair Light Prepared36 — right signatures checked
-- statement:
--   Auxiliary result `PairLightPrepared36.right_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight36.lean, lines 16-18, SHA-256 9100cfea8ccbb4cae74a5787525e16fb16fbcc63c53188bf2450d3232c47a459. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightPrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightPrepared36.right_signatures_checked :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true := by sorry





end D1Bound5.PairLightPrepared36
end
