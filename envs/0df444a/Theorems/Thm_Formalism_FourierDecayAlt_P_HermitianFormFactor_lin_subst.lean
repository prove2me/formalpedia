-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_lin_subst
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.lin_subst
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:19:52.614863+00:00
-- url     : https://prove2.me/theorems/b450e130-17ef-4bd7-a4e8-3c23c13bc5b5
-- title:
--   Hermitian Form Factor: lin subst
-- statement:
--   The Hermitian Form Factor construction uses the lin subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L553-L563
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L553-L563

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

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.lin_subst {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] (L L' : E →ₗ[ℝ] E) (h : L ∘ₗ L' = LinearMap.id) :
    ∃ c : ℝ≥0∞, ∀ f : E → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = c * ∫⁻ x, f (L x) ∂μ := by sorry
