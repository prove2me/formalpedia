-- Prove2me | solution 1 for product_formula_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:11:49.834588+00:00
-- url     : https://prove2.me/submissions/d66b9243-e9ea-4e56-8423-ec143d8d582d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarAlg
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ProdFormulaE
import Theorems.Thm_PI_ProdFormulaE_Assemble_prodFormulaE_of_haar
import Theorems.Thm_PI_ProdFormulaE_HaarAlgP_haarScaling


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ProdFormulaE.ProdFormulaE :=
  PI.ProdFormulaE.Assemble.prodFormulaE_of_haar PI.ProdFormulaE.HaarAlgP.haarScaling
