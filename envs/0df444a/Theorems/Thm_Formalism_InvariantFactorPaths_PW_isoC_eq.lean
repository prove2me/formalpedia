-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_eq
-- name    : Formalism.InvariantFactorPaths.PW.isoC_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:12.589021+00:00
-- url     : https://prove2.me/theorems/6906afcf-9ef4-4d16-83ea-f3f325bbcad4
-- title:
--   PW: iso C eq
-- statement:
--   The PW construction uses the iso C eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L205-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L205-L215

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
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
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}

theorem Formalism.InvariantFactorPaths.PW.isoC_eq (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    IsoC p LL j Cs la =
      (GAe p LL j (enumC Cs)).gS {v | (GAe p LL j (enumC Cs)).IsHW (la ∘ enumC Cs) v} := by sorry
