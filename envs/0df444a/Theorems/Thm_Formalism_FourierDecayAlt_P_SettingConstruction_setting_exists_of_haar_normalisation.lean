-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_setting_exists_of_haar_normalisation
-- name    : Formalism.FourierDecayAlt.P.SettingConstruction.setting_exists_of_haar_normalisation
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:23:39.031804+00:00
-- url     : https://prove2.me/theorems/d20e62c6-2a6c-4da2-8dd4-4dd9d0b2a6f8
-- title:
--   Setting Construction: setting exists of haar normalisation
-- statement:
--   The Setting Construction construction uses the setting exists of haar normalisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L376-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L376-L378

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem Formalism.FourierDecayAlt.P.SettingConstruction.setting_exists_of_haar_normalisation (hG : HaarGExists) (hW : HaarWExists) (hN : HaarNExists) (hI : IntNorm) :
    RealPlaceDataExists ∧ RealPlaceDataNonempty := by sorry
