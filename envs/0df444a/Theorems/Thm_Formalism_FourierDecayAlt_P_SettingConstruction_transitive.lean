-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_transitive
-- name    : Formalism.FourierDecayAlt.P.SettingConstruction.transitive
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:52:57.916515+00:00
-- url     : https://prove2.me/theorems/96d2a918-0c46-4797-86be-34f247cbeea7
-- title:
--   Setting Construction: transitive
-- statement:
--   The Setting Construction construction uses the transitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L83-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L83-L126

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

theorem Formalism.FourierDecayAlt.P.SettingConstruction.transitive (hH : Hᴴ = H) (u v : ι → ℂ) (t : ℝ) (ht : 0 < t) (hu : herm H u u = -(t : ℂ)) (hv : herm H v v = -(t : ℂ)) :
    ∃ g : Matrix ι ι ℂ, gᴴ * H * g = H ∧ g *ᵥ u = v := by sorry
