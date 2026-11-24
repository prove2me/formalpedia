-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_Hb_left
-- name    : Formalism.FourierDecayAlt.P.SettingConstruction.herm_Hb_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:22:54.224418+00:00
-- url     : https://prove2.me/theorems/399dbde7-a846-4ffc-932e-f6c8b0d7186b
-- title:
--   Setting Construction: herm Hb left
-- statement:
--   The Setting Construction construction uses the herm Hb left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L144-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L144-L148

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

theorem Formalism.FourierDecayAlt.P.SettingConstruction.herm_Hb_left (y : Fin (k + 1) → ℂ) (i : Fin (k + 1)) :
    herm (Hb k) (Pi.single i 1) y = (if i = Fin.last k then -1 else 1) * star (y i) := by sorry
