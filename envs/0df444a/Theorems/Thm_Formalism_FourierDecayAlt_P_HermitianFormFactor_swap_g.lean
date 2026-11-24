-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_swap_g
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.swap_g
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:15:45.913546+00:00
-- url     : https://prove2.me/theorems/48974a79-12ce-4af3-8d7a-191a7698adbf
-- title:
--   Hermitian Form Factor: swap g
-- statement:
--   The Hermitian Form Factor construction uses the swap g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1250-L1262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1250-L1262

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

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.swap_g (hH : IsUnit H.det) (ρ : ℝ) {g : m → m → ℂ} (hg : Matrix.of g ∈ UH H) :
    ∫⁻ Y : Q → m → ℂ, Ff H Ep 1 Y * Ff H Ep ρ (act g Y) =
      ∫⁻ Y : Q → m → ℂ, Ff H Ep 1 (act (invF g) Y) * Ff H Ep ρ Y := by sorry
