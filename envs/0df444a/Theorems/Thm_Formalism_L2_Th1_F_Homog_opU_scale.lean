-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Homog_opU_scale
-- name    : Formalism.L2.Th1.F.Homog.opU_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:13.679685+00:00
-- url     : https://prove2.me/theorems/b2fa30d3-c29a-41d6-948b-e2bfaf94cd61
-- title:
--   Homog: op U scale
-- statement:
--   The Homog construction uses the op U scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/LatticeOnly.lean#L321-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/LatticeOnly.lean#L321-L327

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Homog
variable (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)

theorem Formalism.L2.Th1.F.Homog.opU_scale (t z : ℂ) :
    opU (scalePair L c hc) (c * t) (sgStar (scalePair L c hc)) (c * z)
      = c * opU L t (sgStar L) z := by sorry
