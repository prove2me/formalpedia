-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ShearMeasurability_shear_meas
-- name    : Formalism.FourierDecayAlt.P.ShearMeasurability.shear_meas
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:22:42.672306+00:00
-- url     : https://prove2.me/theorems/390df13d-ab06-4191-a1a1-b384c2a3fd24
-- title:
--   Shear Measurability: shear meas
-- statement:
--   The Shear Measurability construction uses the shear meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShearMeasurability.lean#L246-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShearMeasurability.lean#L246-L268

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

theorem Formalism.FourierDecayAlt.P.ShearMeasurability.shear_meas : Measurable (fun x => mulMap w (eSplit w x)) := by sorry
