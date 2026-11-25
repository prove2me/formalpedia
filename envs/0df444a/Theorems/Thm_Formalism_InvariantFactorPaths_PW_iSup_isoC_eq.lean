-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_iSup_isoC_eq
-- name    : Formalism.InvariantFactorPaths.PW.iSup_isoC_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:44:28.105223+00:00
-- url     : https://prove2.me/theorems/6ddda0b3-616a-5596-980a-ef63eb7910ff
-- title:
--   PW: i Sup iso C eq
-- statement:
--   The PW construction uses the i Sup iso C eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L80-L84

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.InvariantFactorPaths.PW.iSup_isoC_eq (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    (⨆ (la' : Fin r → ℤ) (_ : la' ∈ {la' : Fin r → ℤ | ∀ c ∈ Cs, la' c = la c}), IsoC p LL j Cs la') =
      IsoC p LL j Cs la := by sorry
