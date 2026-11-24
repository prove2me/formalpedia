-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_isLocPt_toStd_iff
-- name    : Formalism.FourierDecayAlt.P.PBD.isLocPt_toStd_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:33:48.226506+00:00
-- url     : https://prove2.me/theorems/c316af75-d5b1-4d96-8b9e-1270db94cd2e
-- title:
--   PBD: is Loc Pt to Std iff
-- statement:
--   The PBD construction uses the is Loc Pt to Std iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L42-L45

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped Matrix

theorem Formalism.FourierDecayAlt.P.PBD.isLocPt_toStd_iff (r : ℕ) (g : ℝ) (hg : 0 < g) (p : C.LPt) (b i : ℕ) :
    D.IsLocPt (D.toStd r g b p) i ↔ D.IsLocPt p i := by sorry
