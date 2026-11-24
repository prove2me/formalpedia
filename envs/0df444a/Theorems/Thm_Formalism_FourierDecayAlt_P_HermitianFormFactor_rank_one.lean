-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_rank_one
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.rank_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:15:37.59034+00:00
-- url     : https://prove2.me/theorems/0dcd839f-cb74-4f65-8ea3-8aa2e74b320d
-- title:
--   Hermitian Form Factor: rank one
-- statement:
--   The Hermitian Form Factor construction uses the rank one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L801-L854
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L801-L854

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

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.rank_one (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀) (h0 : ∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₀ T = 0)
    (b : Q → ℂ) :
    ∫⁻ X : Q → Q → ℂ, G₀ (gram X - Matrix.vecMulVec (star b) b) = ∫⁻ X : Q → Q → ℂ, G₀ (gram X) := by sorry
