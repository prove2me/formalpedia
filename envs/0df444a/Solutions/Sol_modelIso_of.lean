-- Prove2me | solution 1 for modelIso_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:48:52.231484+00:00
-- url     : https://prove2.me/submissions/76997f4f-fa3f-4ca2-8c60-86756046059d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_Assembly
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_PolyExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_TorusEigenvalueFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_DetSplit
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HwIrred
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ModelIso
import Theorems.Thm_PI_WMI_determinant_splitting_formula
import Theorems.Thm_PI_WMI_lambda_integrality
import Theorems.Thm_PI_WMI_lower_triangular_invariance
import Theorems.Thm_PI_WMI_modelIso_of_steps
import Theorems.Thm_PI_WMI_model_map_equivariance
import Theorems.Thm_PI_WMI_polyExt_of
import Theorems.Thm_PI_WMI_torus_eigenvalue_formula


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.PolyCoef → PI.UnitaryDense → PI.HwIrred → PI.ModelIso :=
  fun hp hu hh => PI.WMI.modelIso_of_steps (PI.WMI.polyExt_of hp hu) PI.WMI.lambda_integrality
    PI.WMI.torus_eigenvalue_formula PI.WMI.lower_triangular_invariance PI.WMI.model_map_equivariance PI.WMI.determinant_splitting_formula hh
