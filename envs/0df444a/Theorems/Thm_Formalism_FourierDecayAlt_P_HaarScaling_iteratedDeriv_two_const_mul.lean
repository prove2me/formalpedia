-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HaarScaling_iteratedDeriv_two_const_mul
-- name    : Formalism.FourierDecayAlt.P.HaarScaling.iteratedDeriv_two_const_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:54.379871+00:00
-- url     : https://prove2.me/theorems/4581fcd9-0ba4-4876-aeb3-5035a01fe904
-- title:
--   Haar Scaling: iterated Deriv two const mul
-- statement:
--   The Haar Scaling construction uses the iterated Deriv two const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarScaling.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarScaling.lean#L45-L50

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarScaling
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
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HaarScaling
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem Formalism.FourierDecayAlt.P.HaarScaling.iteratedDeriv_two_const_mul (c : ℂ) (f : ℝ → ℂ) :
    iteratedDeriv 2 (fun x => c * f x) = fun x => c * iteratedDeriv 2 f x := by sorry
