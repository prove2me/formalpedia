-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_mid
-- name    : Formalism.FourierDecayAlt.P.SettingConstruction.herm_mid
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:22:40.77974+00:00
-- url     : https://prove2.me/theorems/17210e5c-cf83-4df1-9382-7dc2f588f437
-- title:
--   Setting Construction: herm mid
-- statement:
--   The Setting Construction construction uses the herm mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L292-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L292-L301

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

theorem Formalism.FourierDecayAlt.P.SettingConstruction.herm_mid (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') :
    herm (Hpk k r) z z' = herm (Hb k) (wbPart k r z) (wbPart k r z') := by sorry
