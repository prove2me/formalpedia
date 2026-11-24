-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_unitary_of_form
-- name    : Formalism.FourierDecayAlt.P.SettingConstruction.unitary_of_form
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:22:38.709812+00:00
-- url     : https://prove2.me/theorems/727d9695-02a9-4e80-b74c-56f51182626b
-- title:
--   Setting Construction: unitary of form
-- statement:
--   The Setting Construction construction uses the unitary of form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L64-L67

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

theorem Formalism.FourierDecayAlt.P.SettingConstruction.unitary_of_form (g : Matrix ι ι ℂ) (h : ∀ x y, herm H (g *ᵥ x) (g *ᵥ y) = herm H x y) : gᴴ * H * g = H := by sorry
