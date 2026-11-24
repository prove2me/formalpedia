-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ShearMeasurability_shearMap_apply
-- name    : Formalism.FourierDecayAlt.P.ShearMeasurability.shearMap_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:22:36.098801+00:00
-- url     : https://prove2.me/theorems/9a01b516-6ce0-4ec0-ae32-8d6b3e1879b5
-- title:
--   Shear Measurability: shear Map apply
-- statement:
--   The Shear Measurability construction uses the shear Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShearMeasurability.lean#L150-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShearMeasurability.lean#L150-L211

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

theorem Formalism.FourierDecayAlt.P.ShearMeasurability.shearMap_apply (x : C2.Lidx m → ℂ) (q : C2.Lidx m) :
    mulMap w (eSplit w x) q = x q + ∑ k, aX w x q.1.1 k * bX w x k q.1.2 := by sorry
