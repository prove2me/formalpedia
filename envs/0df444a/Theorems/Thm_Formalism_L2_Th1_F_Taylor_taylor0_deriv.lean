-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_deriv
-- name    : Formalism.L2.Th1.F.Taylor.taylor0_deriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:04.200402+00:00
-- url     : https://prove2.me/theorems/be163b11-546e-4366-8c89-9ea53056262c
-- title:
--   Taylor: taylor0 deriv
-- statement:
--   The Taylor construction uses the taylor0 deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/Taylor.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/Taylor.lean#L56-L62

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
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
open Formalism.L2.Th1.F.Taylor
open PowerSeries

theorem Formalism.L2.Th1.F.Taylor.taylor0_deriv (f : ℂ → ℂ) : taylor0 (deriv f) = derivative ℂ (taylor0 f) := by sorry
