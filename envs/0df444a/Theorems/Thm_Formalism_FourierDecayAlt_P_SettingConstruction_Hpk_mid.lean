-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_Hpk_mid
-- name    : Formalism.FourierDecayAlt.P.SettingConstruction.Hpk_mid
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:21:36.364653+00:00
-- url     : https://prove2.me/theorems/b69be11f-6ed1-4de9-b8d3-b797ad8d392c
-- title:
--   Setting Construction: Hpk mid
-- statement:
--   The Setting Construction construction uses the Hpk mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L288-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L288-L290

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
variable (k r : ℕ)

theorem Formalism.FourierDecayAlt.P.SettingConstruction.Hpk_mid (a b : Fin (k + 1)) : Hpk k r (wI k r a) (wI k r b) = Hb k a b := by sorry
