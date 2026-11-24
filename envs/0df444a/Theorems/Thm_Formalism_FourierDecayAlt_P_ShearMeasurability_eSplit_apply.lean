-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ShearMeasurability_eSplit_apply
-- name    : Formalism.FourierDecayAlt.P.ShearMeasurability.eSplit_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:22:49.967866+00:00
-- url     : https://prove2.me/theorems/c72de372-d384-44a3-9518-5cc83774f221
-- title:
--   Shear Measurability: e Split apply
-- statement:
--   The Shear Measurability construction uses the e Split apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShearMeasurability.lean#L138-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShearMeasurability.lean#L138-L139

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

theorem Formalism.FourierDecayAlt.P.ShearMeasurability.eSplit_apply (x : C2.Lidx m → ℂ) :
    eSplit w x = (fun a => x ⟨a.1, a.2.1⟩, fun b => x ⟨b.1, b.2.1⟩) := by sorry
