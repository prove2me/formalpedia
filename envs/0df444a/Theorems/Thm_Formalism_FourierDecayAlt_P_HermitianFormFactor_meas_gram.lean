-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_meas_gram
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.meas_gram
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:19:28.571804+00:00
-- url     : https://prove2.me/theorems/43d7adec-d8f5-48a1-9f72-52d439391b98
-- title:
--   Hermitian Form Factor: meas gram
-- statement:
--   The Hermitian Form Factor construction uses the meas gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L730-L734
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L730-L734

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

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.meas_gram (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀) :
    Measurable fun X : Q → Q → ℂ => G₀ (gram X) := by sorry
