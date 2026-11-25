-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_lift_of_x_of_parts
-- name    : Formalism.FourierDecayAlt.P.lift_of_x_of_parts
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:02:40.837138+00:00
-- url     : https://prove2.me/theorems/45fc7aef-1b36-41fc-9c82-c4529798be9b
-- title:
--   P: lift of x of parts
-- statement:
--   The P construction uses the lift of x of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftOfXOfParts.lean#L9-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftOfXOfParts.lean#L9-L34

import Definitions.Def_Formalism_HermitianCurvature_StatementTL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftOfXOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr
noncomputable section

theorem Formalism.FourierDecayAlt.P.lift_of_x_of_parts : TL.LiftXOfParts := by sorry
