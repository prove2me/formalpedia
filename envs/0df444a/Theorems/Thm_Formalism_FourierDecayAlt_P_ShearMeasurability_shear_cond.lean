-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ShearMeasurability_shear_cond
-- name    : Formalism.FourierDecayAlt.P.ShearMeasurability.shear_cond
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:22:51.850215+00:00
-- url     : https://prove2.me/theorems/4f3ad708-4575-45c1-bc3e-c8a4961d739b
-- title:
--   Shear Measurability: shear cond
-- statement:
--   The Shear Measurability construction uses the shear cond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShearMeasurability.lean#L213-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShearMeasurability.lean#L213-L244

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

theorem Formalism.FourierDecayAlt.P.ShearMeasurability.shear_cond : ShearCond (gap (m := m)) (fun x => mulMap w (eSplit w x)) := by sorry
