-- Prove2me | solution 1 for isometry_invariant_metric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:12:53.726719+00:00
-- url     : https://prove2.me/submissions/56c0a684-4e61-4563-ba65-5b3c734c3f5a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoInvMetric
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_IsoInvMetricOfHw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_PolyEqZeroOfCircle
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IsoInvMetric
import Theorems.Thm_PI_IsoInvMetricW_hermitian_weight
import Theorems.Thm_PI_IsoInvMetricW_isoInvMetric_of_hw


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.IsoInvMetric.IsoInvMetric :=
  PI.IsoInvMetricW.isoInvMetric_of_hw PI.IsoInvMetricW.hermitian_weight
