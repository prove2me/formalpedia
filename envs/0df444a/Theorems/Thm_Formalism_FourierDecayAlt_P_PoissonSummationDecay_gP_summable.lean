-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_gP_summable
-- name    : Formalism.FourierDecayAlt.P.PoissonSummationDecay.gP_summable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:31:00.968155+00:00
-- url     : https://prove2.me/theorems/497c87a3-9a7c-471e-84ca-6dc4ce0034ab
-- title:
--   Poisson Summation Decay: g P summable
-- statement:
--   The Poisson Summation Decay construction uses the g P summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L173-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L173-L208

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type} [Fintype ι]

theorem Formalism.FourierDecayAlt.P.PoissonSummationDecay.gP_summable [MeasurableSpace V] [BorelSpace V] (π : ι → V →L[ℝ] ℂ)
    (hπ : Function.Bijective fun (c : V) (v : ι) => π v c)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    Summable (fun l : Λ => gP π l) := by sorry
