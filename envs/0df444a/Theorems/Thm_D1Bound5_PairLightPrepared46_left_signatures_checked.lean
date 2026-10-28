-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared46_left_signatures_checked
-- name    : D1Bound5.PairLightPrepared46.left_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:35:59.182409+00:00
-- url     : https://prove2.me/theorems/bac1378c-246d-40e9-8077-6ad0dcd5e13e
-- title:
--   Pair Light Prepared46 — left signatures checked
-- statement:
--   Auxiliary result `PairLightPrepared46.left_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft46.lean, lines 14-16, SHA-256 1f83b52da398d7859b2344f560660efce4764f16abde756d5407b114342d3f4f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_002

section
namespace D1Bound5.PairLightPrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightPrepared46.left_signatures_checked :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true := by sorry





end D1Bound5.PairLightPrepared46
end
