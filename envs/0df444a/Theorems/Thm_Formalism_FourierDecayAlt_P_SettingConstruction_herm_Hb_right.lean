-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_Hb_right
-- name    : Formalism.FourierDecayAlt.P.SettingConstruction.herm_Hb_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:21:47.769804+00:00
-- url     : https://prove2.me/theorems/36c8cb12-a297-46fd-83f4-04a7d15e2e9f
-- title:
--   Setting Construction: herm Hb right
-- statement:
--   The Setting Construction construction uses the herm Hb right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L138-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L138-L142

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
variable (k : ℕ)

theorem Formalism.FourierDecayAlt.P.SettingConstruction.herm_Hb_right (x : Fin (k + 1) → ℂ) (i : Fin (k + 1)) :
    herm (Hb k) x (Pi.single i 1) = (if i = Fin.last k then -1 else 1) * x i := by sorry
