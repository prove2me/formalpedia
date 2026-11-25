-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Homog_quasiPeriodConst_scale
-- name    : Formalism.L2.Th1.F.Homog.quasiPeriodConst_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:19.62514+00:00
-- url     : https://prove2.me/theorems/87538d99-c796-4ad7-8aa0-3ae5c896aef2
-- title:
--   Homog: quasi Period Const scale
-- statement:
--   The Homog construction uses the quasi Period Const scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/LatticeOnly.lean#L281-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/LatticeOnly.lean#L281-L301

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

theorem Formalism.L2.Th1.F.Homog.quasiPeriodConst_scale : s2 (scalePair L c hc) = (c ^ 2)⁻¹ * s2 L := by sorry
