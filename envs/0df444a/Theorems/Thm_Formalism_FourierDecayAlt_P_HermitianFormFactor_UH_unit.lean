-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_UH_unit
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.UH_unit
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:51:36.64702+00:00
-- url     : https://prove2.me/theorems/cdc75ea7-0d5c-43e4-8972-dae0d23fda11
-- title:
--   Hermitian Form Factor: UH unit
-- statement:
--   The Hermitian Form Factor construction uses the UH unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1104-L1110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1104-L1110

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

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.UH_unit (hH : IsUnit H.det) {g : Matrix m m ℂ} (hg : g ∈ UH H) : IsUnit g.det := by sorry
