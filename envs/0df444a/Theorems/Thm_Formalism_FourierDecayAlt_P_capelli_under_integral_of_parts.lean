-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_capelli_under_integral_of_parts
-- name    : Formalism.FourierDecayAlt.P.capelli_under_integral_of_parts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:38:55.394048+00:00
-- url     : https://prove2.me/theorems/d9dbbd90-bc7f-4aec-b6ef-f8c69f90b9ab
-- title:
--   P: capelli under integral of parts
-- statement:
--   The P construction uses the capelli under integral of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordKeyIdentity.lean#L71-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordKeyIdentity.lean#L71-L92

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.capelli_under_integral_of_parts : Formalism.FourierDecayAlt.JF.CVUnderIntOfParts := by sorry
