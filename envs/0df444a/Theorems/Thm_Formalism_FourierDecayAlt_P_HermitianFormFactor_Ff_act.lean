-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Ff_act
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.Ff_act
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:19:21.310545+00:00
-- url     : https://prove2.me/theorems/f545a207-17ad-4b6b-9831-a7c7d4582d27
-- title:
--   Hermitian Form Factor: Ff act
-- statement:
--   The Hermitian Form Factor construction uses the Ff act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1144-L1171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1144-L1171

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

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.Ff_act (F : Frame H Ep Em) {ρ σ : ℝ} {Y : Q → m → ℂ} (hY : tb H Ep Y ∈ Kset P Q σ) {gY : Matrix m m ℂ}
    {a : Matrix Q Q ℂ} (hgY : gY ∈ UH H) (ha : IsUnit a.det) (hYe : cm Y = gY * Em * a) {g : m → m → ℂ}
    (hg : Matrix.of g ∈ UH H) :
    Ff H Ep ρ (act g Y) = (Bset Ep Em ρ).indicator 1 (rmF gY g) := by sorry
