-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_const
-- name    : Formalism.L2.Th1.F.Taylor.taylor0_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:33.262799+00:00
-- url     : https://prove2.me/theorems/c09a7043-996b-43b9-9e89-e31c281bdcd6
-- title:
--   Taylor: taylor0 const
-- statement:
--   The Taylor construction uses the taylor0 const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/Taylor.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/Taylor.lean#L38-L43

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

theorem Formalism.L2.Th1.F.Taylor.taylor0_const (c : ℂ) : taylor0 (fun _ => c) = C c := by sorry
