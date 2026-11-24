-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_ptEntry_app_last
-- name    : Formalism.FourierDecayAlt.P.PBD.ptEntry_app_last
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:34:28.736722+00:00
-- url     : https://prove2.me/theorems/76628896-95d9-4093-a11d-210677fee985
-- title:
--   PBD: pt Entry app last
-- statement:
--   The PBD construction uses the pt Entry app last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L123-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L123-L136

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

theorem Formalism.FourierDecayAlt.P.PBD.ptEntry_app_last (c : ℂ) : ∀ (H : C.LPt), D.ptEntry (H ++ [(1, c)]) (D.ptSize H) (D.ptSize H) = c
  := by sorry
