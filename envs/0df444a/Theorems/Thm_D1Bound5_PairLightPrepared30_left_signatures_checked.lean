-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared30_left_signatures_checked
-- name    : D1Bound5.PairLightPrepared30.left_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:36:17.529585+00:00
-- url     : https://prove2.me/theorems/e821ac66-cd1b-40b4-9890-d8e22ff57c44
-- title:
--   Pair Light Prepared30 — left signatures checked
-- statement:
--   Auxiliary result `PairLightPrepared30.left_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft30.lean, lines 15-17, SHA-256 f0545c637117e4b165720807970cfb9a189609107726725565549e0bba82bee3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightPrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightPrepared30.left_signatures_checked :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true := by sorry





end D1Bound5.PairLightPrepared30
end
