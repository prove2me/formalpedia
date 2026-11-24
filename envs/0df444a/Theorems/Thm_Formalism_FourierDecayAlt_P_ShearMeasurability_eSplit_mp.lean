-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ShearMeasurability_eSplit_mp
-- name    : Formalism.FourierDecayAlt.P.ShearMeasurability.eSplit_mp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:23:06.322061+00:00
-- url     : https://prove2.me/theorems/9d80157c-481b-4488-8e5a-ce66a7e55278
-- title:
--   Shear Measurability: e Split mp
-- statement:
--   The Shear Measurability construction uses the e Split mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShearMeasurability.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShearMeasurability.lean#L134-L136

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShearMeasurability
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.ShearMeasurability
variable {m : ℕ} (w : Equiv.Perm (Fin m))

theorem Formalism.FourierDecayAlt.P.ShearMeasurability.eSplit_mp : MeasurePreserving (eSplit w) volume volume := by sorry
