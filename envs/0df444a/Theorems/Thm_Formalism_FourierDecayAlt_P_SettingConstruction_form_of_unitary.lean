-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_form_of_unitary
-- name    : Formalism.FourierDecayAlt.P.SettingConstruction.form_of_unitary
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:21:41.225777+00:00
-- url     : https://prove2.me/theorems/158d2ed3-caeb-4322-8e68-3c65970a40ef
-- title:
--   Setting Construction: form of unitary
-- statement:
--   The Setting Construction construction uses the form of unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L69-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L69-L70

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
variable [DecidableEq ι]

theorem Formalism.FourierDecayAlt.P.SettingConstruction.form_of_unitary {g : Matrix ι ι ℂ} (h : gᴴ * H * g = H) (x y : ι → ℂ) : herm H (g *ᵥ x) (g *ᵥ y) = herm H x y := by sorry
