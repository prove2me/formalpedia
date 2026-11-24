-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ShearMeasurability_lvl_mp
-- name    : Formalism.FourierDecayAlt.P.ShearMeasurability.lvl_mp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:23:10.426967+00:00
-- url     : https://prove2.me/theorems/e8b3cddf-163e-47ca-a33e-b998259b419b
-- title:
--   Shear Measurability: lvl mp
-- statement:
--   The Shear Measurability construction uses the lvl mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShearMeasurability.lean#L42-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShearMeasurability.lean#L42-L85

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Formalism.FourierDecayAlt.P.ShearMeasurability.lvl_mp {ρ : ι → ℕ} {F : (ι → ℂ) → ι → ℂ} (hFm : Measurable F) (hF : ShearCond ρ F) (n : ℕ) :
    MeasurePreserving (lvl ρ F n) volume volume := by sorry
