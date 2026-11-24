-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_vol_core
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.vol_core
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:55:10.926652+00:00
-- url     : https://prove2.me/theorems/bd88087e-885a-4d87-816f-46480ad99c84
-- title:
--   Hermitian Form Factor: vol core
-- statement:
--   The Hermitian Form Factor construction uses the vol core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1625-L1637
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1625-L1637

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_right

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

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.vol_core (F : Frame H Ep Em) (hH : IsUnit H.det) (μ : Measure (m → m → ℂ)) [SFinite μ]
    (conc : ∀ᵐ g ∂μ, Matrix.of g ∈ UH H)
    (left : ∀ a ∈ UH H, μ.map (lmF a) = μ) (right : ∀ a ∈ UH H, μ.map (rmF a) = μ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    μ (Bset Ep Em ρ) = μ (invF ⁻¹' Bset Ep Em 1) * ENNReal.ofReal (ρ ^ (2 * Fintype.card P * Fintype.card Q)) := by sorry
