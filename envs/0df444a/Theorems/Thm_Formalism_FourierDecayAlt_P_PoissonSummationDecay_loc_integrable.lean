-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_loc_integrable
-- name    : Formalism.FourierDecayAlt.P.PoissonSummationDecay.loc_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:59.151893+00:00
-- url     : https://prove2.me/theorems/d1e98c79-ad3b-403b-bc46-9fb4b365986b
-- title:
--   Poisson Summation Decay: loc integrable
-- statement:
--   The Poisson Summation Decay construction uses the loc integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L68-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L68-L91

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

theorem Formalism.FourierDecayAlt.P.PoissonSummationDecay.loc_integrable (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (φ : V → ℂ)
    (hc : Continuous φ) (h : LocSummable Λ φ) : Integrable φ := by sorry
