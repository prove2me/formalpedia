-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_compactly_supported_monotone
-- name    : Formalism.FourierDecayAlt.P.compactly_supported_monotone
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:38:43.958511+00:00
-- url     : https://prove2.me/theorems/61baf769-db24-4afc-b8da-f615b09a242f
-- title:
--   P: compactly supported monotone
-- statement:
--   The P construction uses the compactly supported monotone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SeminormCompletion.lean#L597-L597
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SeminormCompletion.lean#L597-L597

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.compactly_supported_monotone : Formalism.FourierDecayAlt.U.CCMono := by sorry
