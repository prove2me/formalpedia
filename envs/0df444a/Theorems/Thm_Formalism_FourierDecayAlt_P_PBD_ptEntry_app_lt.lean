-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_ptEntry_app_lt
-- name    : Formalism.FourierDecayAlt.P.PBD.ptEntry_app_lt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:32:38.600851+00:00
-- url     : https://prove2.me/theorems/6e504fc3-4b83-460b-ae46-b5cd8a6155c8
-- title:
--   PBD: pt Entry app lt
-- statement:
--   The PBD construction uses the pt Entry app lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L109-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L109-L121

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

theorem Formalism.FourierDecayAlt.P.PBD.ptEntry_app_lt (c : ℂ) : ∀ (H : C.LPt) (a b : ℕ), a < D.ptSize H → b < D.ptSize H →
    D.ptEntry (H ++ [(1, c)]) a b = D.ptEntry H a b
  := by sorry
