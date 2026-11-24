-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_UH_inv
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.UH_inv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:52:30.874807+00:00
-- url     : https://prove2.me/theorems/3f78195d-e357-497a-9c0f-dbe95973a54d
-- title:
--   Hermitian Form Factor: UH inv
-- statement:
--   The Hermitian Form Factor construction uses the UH inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1112-L1118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1112-L1118

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

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.UH_inv (hH : IsUnit H.det) {g : Matrix m m ℂ} (hg : g ∈ UH H) : g⁻¹ ∈ UH H := by sorry
