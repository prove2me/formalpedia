-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared38_right_signatures_checked
-- name    : D1Bound5.PairLightPrepared38.right_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:11:57.136835+00:00
-- url     : https://prove2.me/theorems/d5df2ce1-31ba-4be8-9d62-10bc10dda91d
-- title:
--   Pair Light Prepared38 — right signatures checked
-- statement:
--   Auxiliary result `PairLightPrepared38.right_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight38.lean, lines 13-15, SHA-256 4124fc847de5ef6d667df883652750a2c8c5beac8946c20a5f389b2ad11f6881. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_004

section
namespace D1Bound5.PairLightPrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightPrepared38.right_signatures_checked :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true := by sorry





end D1Bound5.PairLightPrepared38
end
