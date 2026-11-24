-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_translated_product_integrable_bound
-- name    : Formalism.FourierDecayAlt.P.B6.translated_product_integrable_bound
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:59:29.673101+00:00
-- url     : https://prove2.me/theorems/98d05aae-66d5-436e-811f-758aa869d10a
-- title:
--   B6: translated product integrable bound
-- statement:
--   The B6 construction uses the translated product integrable bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L888-L921
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L888-L921

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}

theorem Formalism.FourierDecayAlt.P.B6.translated_product_integrable_bound (H : Hyp D Ξ α) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (A B : Mat k r → (Wq →L[ℂ] Wp)) (cA cB : ℝ),
    admitted α cA A → admitted α cB B → ∀ x ∈ GV k r, ∀ y ∈ GV k r,
      Integrable (fun g : Mt k r => ‖A (x⁻¹ * Matrix.of g * y)‖ * ‖B (Matrix.of g)‖) D.μG ∧
      (∫ g : Mt k r, ‖A (x⁻¹ * Matrix.of g * y)‖ * ‖B (Matrix.of g)‖ ∂D.μG) ≤
        K * cA * cB * ((Ξ x : ℝ) * (Ξ y : ℝ)) := by sorry
