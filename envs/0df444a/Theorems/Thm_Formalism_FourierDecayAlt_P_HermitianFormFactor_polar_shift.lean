-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_polar_shift
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.polar_shift
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:15:45.949313+00:00
-- url     : https://prove2.me/theorems/949c636b-d906-4847-85f4-bd67bd671caf
-- title:
--   Hermitian Form Factor: polar shift
-- statement:
--   The Hermitian Form Factor construction uses the polar shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L525-L540
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L525-L540

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.polar_shift (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (h0 : ∀ s ≤ 0, φ s = 0) :
    ∫⁻ z : ℂ, φ (Complex.normSq z - 1) = ∫⁻ z : ℂ, φ (Complex.normSq z) := by sorry
