-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lint_smul3
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.lint_smul3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:02:43.991485+00:00
-- url     : https://prove2.me/theorems/7a3f5237-d033-485f-b2de-817c65c1f2d0
-- title:
--   Long Weyl Element: lint smul3
-- statement:
--   The Long Weyl Element construction uses the lint smul3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L965-L975
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L965-L975

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
variable {k r r' : ℕ}

theorem Formalism.FourierDecayAlt.P.LongWeylElement.lint_smul3 {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [SFinite μ]
    [SFinite ν] (a b : ℝ≥0) (F : (α × α) × β → ℝ≥0∞) :
    ∫⁻ p, F p ∂(((a • μ).prod (a • μ)).prod (b • ν)) = ((a * a * b : ℝ≥0) : ℝ≥0∞) * ∫⁻ p, F p ∂((μ.prod μ).prod ν) := by sorry
