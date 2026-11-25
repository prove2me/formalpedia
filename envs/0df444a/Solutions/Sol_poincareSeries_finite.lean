-- Prove2me | solution 1 for poincareSeries_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:12:02.079882+00:00
-- url     : https://prove2.me/submissions/420181e6-8c3c-40f2-afe9-0517de44de7e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientIntegralBound_QuotientLIntegralLeMultiplicityLIntegral
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PoincareSeriesFinite
import Theorems.Thm_PI_PoincareSeriesFinite_UnitaryGroupMassFormula_poincareSeriesFinite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesFinite G μ :=
  PI.PoincareSeriesFinite.UnitaryGroupMassFormula.poincareSeriesFinite G μ
