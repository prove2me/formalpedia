-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_sub_right
-- name    : Formalism.FourierDecayAlt.P.SettingConstruction.herm_sub_right
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:22:32.021493+00:00
-- url     : https://prove2.me/theorems/d28368fe-ac6c-422d-9d09-29280c91eec6
-- title:
--   Setting Construction: herm sub right
-- statement:
--   The Setting Construction construction uses the herm sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L45-L46

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SettingConstruction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

theorem Formalism.FourierDecayAlt.P.SettingConstruction.herm_sub_right (u w w' : ι → ℂ) : herm H u (w - w') = herm H u w - herm H u w' := by sorry
