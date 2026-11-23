-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_loc_cont
-- name    : Formalism.FourierDecayAlt.P.PoissonSummationDecay.loc_cont
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:54.245801+00:00
-- url     : https://prove2.me/theorems/9641ca2a-e711-4295-832e-4d2e4d38b1ba
-- title:
--   Poisson Summation Decay: loc cont
-- statement:
--   The Poisson Summation Decay construction uses the loc cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L51-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L51-L58

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PoissonSummationDecay
open Formalism.FourierDecayAlt.F7
open Finset Polynomial
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace ENNReal
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]
omit [MeasurableSpace V] [BorelSpace V]

theorem Formalism.FourierDecayAlt.P.PoissonSummationDecay.loc_cont (Λ : Submodule ℤ V) (φ : V → ℂ) (hc : Continuous φ) (h : LocSummable Λ φ) :
    Continuous (fun x : V => ∑' l : Λ, φ ((l:V) + x)) := by sorry
