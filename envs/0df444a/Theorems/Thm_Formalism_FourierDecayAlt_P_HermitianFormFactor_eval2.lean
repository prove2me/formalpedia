-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_eval2
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.eval2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:54:54.411054+00:00
-- url     : https://prove2.me/theorems/d70a51a6-8ea1-4a17-8382-477c7af9f093
-- title:
--   Hermitian Form Factor: eval2
-- statement:
--   The Hermitian Form Factor construction uses the eval2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1273-L1286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1273-L1286

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_left

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

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.eval2 (F : Frame H Ep Em) (hH : IsUnit H.det) (μ : Measure (m → m → ℂ)) [SFinite μ]
    (conc : ∀ᵐ g ∂μ, Matrix.of g ∈ UH H) (left : ∀ a ∈ UH H, μ.map (lmF a) = μ) (ρ : ℝ) :
    ∫⁻ g, (∫⁻ Y : Q → m → ℂ, Ff H Ep 1 Y * Ff H Ep ρ (act g Y)) ∂μ =
      Lv H Ep Q ρ * μ (invF ⁻¹' Bset Ep Em 1) := by sorry
