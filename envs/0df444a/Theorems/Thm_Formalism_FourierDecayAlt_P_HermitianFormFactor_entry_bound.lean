-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_entry_bound
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.entry_bound
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:14:36.424798+00:00
-- url     : https://prove2.me/theorems/1cc4e765-d1e4-46f5-ac54-9593ef892fcb
-- title:
--   Hermitian Form Factor: entry bound
-- statement:
--   The Hermitian Form Factor construction uses the entry bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1474-L1498
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1474-L1498

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

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.entry_bound (C : Matrix P Q ℂ) (M : Matrix Q Q ℂ) (hC : ∑ i, ∑ j, Complex.normSq (C i j) ≤ 1)
    (hM : ∑ i, ∑ j, Complex.normSq (M i j) ≤ 1) (i : P) (j : Q) : ‖(C * M) i j‖ ≤ 1 := by sorry
