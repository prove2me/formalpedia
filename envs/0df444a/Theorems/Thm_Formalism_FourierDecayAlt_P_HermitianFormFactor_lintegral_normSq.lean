-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_lintegral_normSq
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.lintegral_normSq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:16:19.394027+00:00
-- url     : https://prove2.me/theorems/a9577657-7be3-40e2-9b90-ec7fb4b9f48f
-- title:
--   Hermitian Form Factor: lintegral norm Sq
-- statement:
--   The Hermitian Form Factor construction uses the lintegral norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L489-L523
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L489-L523

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

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.lintegral_normSq (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ z : ℂ, ψ (Complex.normSq z) = ENNReal.ofReal Real.pi * ∫⁻ s in Set.Ioi (0 : ℝ), ψ s := by sorry
