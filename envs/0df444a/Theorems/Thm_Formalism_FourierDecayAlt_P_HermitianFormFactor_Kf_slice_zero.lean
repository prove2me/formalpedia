-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Kf_slice_zero
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.Kf_slice_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:13:34.005939+00:00
-- url     : https://prove2.me/theorems/2553060d-7ebe-486e-84e6-a488539428fa
-- title:
--   Hermitian Form Factor: Kf slice zero
-- statement:
--   The Hermitian Form Factor construction uses the Kf slice zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1390-L1395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1390-L1395

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
open scoped Pointwise

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.Kf_slice_zero {T : Q → Q → ℂ} (hT : ¬ ((Matrix.of T).PosDef ∧ (Matrix.trace (Matrix.of T)).re ≤ 1)) (σ : ℝ)
    (B : Q → P → ℂ) : Kf P Q σ (T, B) = 0 := by sorry
