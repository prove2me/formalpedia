-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_bSt_append_one
-- name    : Formalism.FourierDecayAlt.P.PBD.bSt_append_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:34:25.242858+00:00
-- url     : https://prove2.me/theorems/e7626810-b360-4476-82b4-5f15671f7a1d
-- title:
--   PBD: b St append one
-- statement:
--   The PBD construction uses the b St append one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L47-L48

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

theorem Formalism.FourierDecayAlt.P.PBD.bSt_append_one (κ : ℝ) (h : C.LPt) (c : ℂ) : D.bSt κ (h ++ [(1, c)]) = D.bSt κ h := by sorry
