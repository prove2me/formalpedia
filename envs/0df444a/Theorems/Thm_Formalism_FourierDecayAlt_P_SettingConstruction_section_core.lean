-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_section_core
-- name    : Formalism.FourierDecayAlt.P.SettingConstruction.section_core
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:22:51.92763+00:00
-- url     : https://prove2.me/theorems/d3e50090-e7ce-476d-b930-e3a8e414b5c6
-- title:
--   Setting Construction: section core
-- statement:
--   The Setting Construction construction uses the section core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L189-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L189-L267

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
open scoped ContDiff

theorem Formalism.FourierDecayAlt.P.SettingConstruction.section_core (hk : 1 ≤ k) (a b : Fin (k + 1) → ℂ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T')
    (ha : herm (Hb k) a a = -(T : ℂ)) (hb : herm (Hb k) b b = -(T' : ℂ)) :
    ∃ μ : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ,
      (∀ i j, ContDiffOn ℝ ∞ (fun ζ => μ ζ i j) {ζ : ℂ | T * T' < Complex.normSq ζ}) ∧
      ∀ ζ : ℂ, T * T' < Complex.normSq ζ →
        (μ ζ)ᴴ * Hb k * μ ζ = Hb k ∧ herm (Hb k) (μ ζ *ᵥ b) a = ζ := by sorry
