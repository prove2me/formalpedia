-- Prove2me | Theorems.Thm_D1Bound5_pairLightIndexedWitnessesCheckedBool_of_prefix_drop
-- name    : D1Bound5.pairLightIndexedWitnessesCheckedBool_of_prefix_drop
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:35.602617+00:00
-- url     : https://prove2.me/theorems/4ff20e41-bf5b-4f13-b57d-c637e76ba9c7
-- title:
--   Pair Light Indexed Witnesses Checked Bool of prefix drop
-- statement:
--   Auxiliary result `pairLightIndexedWitnessesCheckedBool_of_prefix_drop` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PairLightClosure.lean, lines 97-107, SHA-256 ef69d3a60e5b156fbd56cb019ebd0325abef2ca7d10021397aca371566944128. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions

section
namespace D1Bound5

/- Exact coordinate-only version of the indexed closure checker. Mathematical
soundness is established in PairLightClosureBridge, not assumed here. -/





















theorem _root_.D1Bound5.pairLightIndexedWitnessesCheckedBool_of_prefix_drop (tau nu : Int)
    (a b r0 : PairLightCoordinate) (bound : Int) (vertices : List PairLightCoordinate)
    (n : Nat) (witnesses : List PairLightRootWitness)
    (destinations : List (Option Nat × Option Nat))
    (hprefix : pairLightIndexedWitnessesPrefixBool tau nu a b r0 bound vertices n
      witnesses destinations = true)
    (htail : pairLightIndexedWitnessesCheckedBool tau nu a b r0 bound vertices
      (witnesses.drop n) (destinations.drop n) = true) :
    pairLightIndexedWitnessesCheckedBool tau nu a b r0 bound vertices witnesses destinations = true := by sorry

end D1Bound5
end
