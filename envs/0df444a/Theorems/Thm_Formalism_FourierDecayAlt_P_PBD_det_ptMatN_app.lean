-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_det_ptMatN_app
-- name    : Formalism.FourierDecayAlt.P.PBD.det_ptMatN_app
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:34:12.636825+00:00
-- url     : https://prove2.me/theorems/e891a2cd-6b13-4124-9c7b-d11fc2f8ed33
-- title:
--   PBD: det pt Mat N app
-- statement:
--   The PBD construction uses the det pt Mat N app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L154-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L154-L178

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

theorem Formalism.FourierDecayAlt.P.PBD.det_ptMatN_app (c : ℂ) (H : C.LPt) (n : ℕ) (hn : D.ptSize H = n) :
    (D.ptMatN (H ++ [(1, c)]) (n + 1)).det = c * (D.ptMatN H n).det ∧
      D.ptMatN (H ++ [(1, c)]) n = D.ptMatN H n := by sorry
