-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_slice_threshold_bound
-- name    : Formalism.FourierDecayAlt.P.slice_threshold_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:36:01.484057+00:00
-- url     : https://prove2.me/theorems/233ff786-c281-409f-b5c8-be9d8f12fec9
-- title:
--   P: slice threshold bound
-- statement:
--   The P construction uses the slice threshold bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerFourthCondition.lean#L13-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerFourthCondition.lean#L13-L30

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.slice_threshold_bound : C2.SliceThresholdBound := by sorry
