-- Prove2me | solution 1 for hecke_product_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:17:27.893431+00:00
-- url     : https://prove2.me/submissions/94fb9bf1-4f76-4430-982a-bb23ee9fe5c4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_PvLocalSelf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HeckeProd
import Theorems.Thm_PI_HeckeProdW_productRule


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), χ.ProductRule :=
  fun _ _ _ χ => PI.HeckeProdW.productRule χ
