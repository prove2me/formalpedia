-- Prove2me | Theorems.Thm_Formalism_H_PoissonPeriodization_summable_one_add_norm
-- name    : Formalism.H.PoissonPeriodization.summable_one_add_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:43.55175+00:00
-- url     : https://prove2.me/theorems/41c86bfc-6660-41bb-ad02-c3289d3aa1d9
-- title:
--   Poisson Periodization: summable one add norm
-- statement:
--   The Poisson Periodization construction uses the summable one add norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/Periodization.lean#L79-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/Periodization.lean#L79-L98

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Periodization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex Metric
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
open Formalism.H.PoissonPeriodization
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem Formalism.H.PoissonPeriodization.summable_one_add_norm (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {b : ℝ} (hb : (Module.finrank ℝ V : ℝ) < b) :
    Summable (fun l : Λ => (1 + ‖(l : V)‖) ^ (-b)) := by sorry
