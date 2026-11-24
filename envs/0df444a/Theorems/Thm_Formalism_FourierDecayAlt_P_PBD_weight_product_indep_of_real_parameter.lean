-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_weight_product_indep_of_real_parameter
-- name    : Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:46:52.674083+00:00
-- url     : https://prove2.me/theorems/8653297e-81a0-4c59-adb9-3c2e21ea0f04
-- title:
--   PBD: weight product indep of real parameter
-- statement:
--   The PBD construction uses the weight product indep of real parameter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L72-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L72-L84

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

theorem Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter (k r : ℕ) (GG GG' : ℝ) (fr : ℕ → ℕ → ℝ) : ∀ (h : C.LPt) (b : ℕ), 1 ≤ b →
    b + D.ptSize h ≤ r + 1 → C.nAux k r GG fr b h = C.nAux k r GG' fr b h
  := by sorry
