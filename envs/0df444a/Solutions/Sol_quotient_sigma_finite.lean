-- Prove2me | solution 1 for quotient_sigma_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:09:24.864124+00:00
-- url     : https://prove2.me/submissions/8e6276f6-38e8-4399-a10a-d0909915e85c

import Definitions.Def_Formalism_PeriodIntegrals_QuotNuSigma
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientSigmaFiniteness_SigmaFiniteOfWeil
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QuotNuSigma
import Theorems.Thm_PI_UnitaryGroupMassFormula_QuotNuSigma_sigmaFinite_of_weil


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.QuotNuSigma.Target :=
  fun _ _ _ _ _ _ _ _ _ μG _ A B μA μB ν hA hB hW =>
    PI.UnitaryGroupMassFormula.QuotNuSigma.sigmaFinite_of_weil μG A B μA μB ν hA hB hW
