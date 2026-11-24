-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_weight_product_append
-- name    : Formalism.FourierDecayAlt.P.PBD.weight_product_append
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:33:25.524207+00:00
-- url     : https://prove2.me/theorems/cd112fbd-5cea-40a7-a7e4-d2352f54a880
-- title:
--   PBD: weight product append
-- statement:
--   The PBD construction uses the weight product append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L65-L70

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

theorem Formalism.FourierDecayAlt.P.PBD.weight_product_append (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) (x : ℕ × ℂ) : ∀ (h : C.LPt) (b : ℕ),
    C.nAux k r GG fr b (h ++ [x]) = C.nAux k r GG fr b h * C.nAux k r GG fr (b + D.ptSize h) [x]
  := by sorry
