-- Prove2me | Theorems.Thm_Formalism_H_poissonDecay_of
-- name    : Formalism.H.poissonDecay_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:46.875802+00:00
-- url     : https://prove2.me/theorems/38e5b19b-66c0-44db-9efb-b87ad2a2cda1
-- title:
--   H: poisson Decay of
-- statement:
--   The H construction uses the poisson Decay of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/Assembly.lean#L18-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/Assembly.lean#L18-L48

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Assembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem Formalism.H.poissonDecay_of (hD : DualIsLattice V) (h1 : LatticeSummableDecay V)
    (h2 : Periodization V) (h3 : UnfoldCoeff V) (h4 : LatticeFourierSeries V) : PoissonDecay V := by sorry
