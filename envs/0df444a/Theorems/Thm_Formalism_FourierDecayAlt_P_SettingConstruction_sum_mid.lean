-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_sum_mid
-- name    : Formalism.FourierDecayAlt.P.SettingConstruction.sum_mid
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:22:54.71346+00:00
-- url     : https://prove2.me/theorems/7b29063d-cd1d-4eb8-b91d-d33b68a0a46d
-- title:
--   Setting Construction: sum mid
-- statement:
--   The Setting Construction construction uses the sum mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L274-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L274-L286

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

theorem Formalism.FourierDecayAlt.P.SettingConstruction.sum_mid (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → f i = 0) :
    ∑ i, f i = ∑ j : Fin (k + 1), f (wI k r j) := by sorry
