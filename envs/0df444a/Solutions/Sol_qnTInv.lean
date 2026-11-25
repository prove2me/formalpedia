-- Prove2me | solution 1 for qnTInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:01:15.211189+00:00
-- url     : https://prove2.me/submissions/69a860dd-6a6b-483b-a5d0-e9595962cad1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_QnTInvOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnMinorLeft
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnEabPres
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnEabGl
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovLin
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovDet
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovHat
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CovariantHatSqOfLin
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnTInv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_qnTInv_of
import Theorems.Thm_PI_contractionsCovariant_iff
import Theorems.Thm_covariant_det_of_lin
import Theorems.Thm_covariant_hat_of_lin
import Theorems.Thm_covariant_hat_sq_of_lin
import Theorems.Thm_covariant_linear
import Theorems.Thm_qnEabGl
import Theorems.Thm_qnEabPres
import Theorems.Thm_qnMinorLeft


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.Q.TInvariant :=
  Formalism.FourierDecayAlt.Q.TInvW.qnTInv_of
    (PI.contractionsCovariant_iff.2
      ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩)
    qnEabPres qnEabGl qnMinorLeft
