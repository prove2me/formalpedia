-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_meas_gram_sub
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.meas_gram_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:18:45.360949+00:00
-- url     : https://prove2.me/theorems/6ec16c8e-e015-44d4-8626-f062772e0e16
-- title:
--   Hermitian Form Factor: meas gram sub
-- statement:
--   The Hermitian Form Factor construction uses the meas gram sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L723-L728
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L723-L728

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
variable {Q : Type} [Fintype Q] [DecidableEq Q]

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.meas_gram_sub (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀) (C : Matrix Q Q ℂ) :
    Measurable fun X : Q → Q → ℂ => G₀ (gram X - C) := by sorry
