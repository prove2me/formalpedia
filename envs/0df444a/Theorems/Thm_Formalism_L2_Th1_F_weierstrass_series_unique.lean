-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_weierstrass_series_unique
-- name    : Formalism.L2.Th1.F.weierstrass_series_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:09:24.049977+00:00
-- url     : https://prove2.me/theorems/9cecd4a6-9fce-4ed0-8485-a5a6d99571e6
-- title:
--   F: weierstrass series unique
-- statement:
--   The F construction uses the weierstrass series unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorWp.lean#L87-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorWp.lean#L87-L137

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open PowerSeries
open TaylorWp

theorem Formalism.L2.Th1.F.weierstrass_series_unique : IsWpUnique := by sorry
