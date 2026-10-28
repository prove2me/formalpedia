-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_signatures_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:34:59.875338+00:00
-- url     : https://prove2.me/theorems/bffced70-1be3-4117-87ca-b32ea6bbed79
-- title:
--   Pair Light Adaptive Prepared30 — left signatures checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared30.left_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation30.lean, lines 11-14, SHA-256 11a024af2a26b4ebfc0a85daa7b7597218e5054c96e234a4d05934a663f33464. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_signatures_checked :
    (PairLightPrepared30.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared30.sieve x.1)) = true := by sorry






end D1Bound5.PairLightAdaptivePrepared30
end
