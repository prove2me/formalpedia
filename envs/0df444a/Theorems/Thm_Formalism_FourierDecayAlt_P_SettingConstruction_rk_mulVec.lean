-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_rk_mulVec
-- name    : Formalism.FourierDecayAlt.P.SettingConstruction.rk_mulVec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:23:04.299194+00:00
-- url     : https://prove2.me/theorems/8f8bf444-bf4f-410f-aeff-37a39043ab6a
-- title:
--   Setting Construction: rk mul Vec
-- statement:
--   The Setting Construction construction uses the rk mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L74-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L74-L81

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

theorem Formalism.FourierDecayAlt.P.SettingConstruction.rk_mulVec (d : ι → ℂ) (θ β : ℂ) (x : ι → ℂ) : rk H d θ β *ᵥ x = θ • x + (β * herm H x d) • d := by sorry
