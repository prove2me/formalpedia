-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_shear_finset
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.shear_finset
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:15:18.621564+00:00
-- url     : https://prove2.me/theorems/e9d8c679-b9c7-4f15-9ac0-61536925a4d2
-- title:
--   Hermitian Form Factor: shear finset
-- statement:
--   The Hermitian Form Factor construction uses the shear finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L862-L890
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L862-L890

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
variable {P Q : Type} [Fintype P] [Fintype Q] [DecidableEq Q]

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.shear_finset (B : Matrix P Q ℂ) (s : Finset P) :
    ∀ (G₀ : (Q → Q → ℂ) → ℝ≥0∞), Measurable G₀ → (∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₀ T = 0) →
    ∫⁻ X : Q → Q → ℂ, G₀ (gram X - ∑ i ∈ s, Matrix.vecMulVec (star (B i)) (B i)) = ∫⁻ X : Q → Q → ℂ, G₀ (gram X) := by sorry
