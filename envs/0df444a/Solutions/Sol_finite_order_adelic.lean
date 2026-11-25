-- Prove2me | solution 1 for finite_order_adelic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:30:24.301089+00:00
-- url     : https://prove2.me/submissions/6234aad3-1715-4c4d-9f94-868761f27aab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicFiniteOrder_Assembly
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnitKron
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PowBddInt
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TensCpctDen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DefPosDef
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FinOrdAd
import Theorems.Thm_PI_finOrdAd_of
import Theorems.Thm_positive_definite_form
import Theorems.Thm_power_bounded_integral
import Theorems.Thm_tensor_compact_dense
import Theorems.Thm_unit_kronecker


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.FinOrdAd :=
  PI.finOrdAd_of unit_kronecker power_bounded_integral tensor_compact_dense positive_definite_form
