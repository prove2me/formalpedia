-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_ptG_app
-- name    : Formalism.FourierDecayAlt.P.PBD.ptG_app
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:33:41.94141+00:00
-- url     : https://prove2.me/theorems/a192a140-1782-412f-ad80-4cd8129f573a
-- title:
--   PBD: pt G app
-- statement:
--   The PBD construction uses the pt G app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L180-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L180-L185

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

theorem Formalism.FourierDecayAlt.P.PBD.ptG_app (TT : ℝ) (c : ℂ) (H : C.LPt) (n : ℕ) (hn : D.ptSize H = n) :
    D.ptG TT n (H ++ [(1, c)]) = Complex.normSq (D.ptMatN H n).det * (Complex.normSq c - TT) := by sorry
