-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_inj
-- name    : Formalism.L2.Th1.F.Taylor.taylor0_inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:17.231035+00:00
-- url     : https://prove2.me/theorems/724c6e0a-b049-4dbf-8fae-61572029e4f9
-- title:
--   Taylor: taylor0 inj
-- statement:
--   The Taylor construction uses the taylor0 inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/Taylor.lean#L90-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/Taylor.lean#L90-L108

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

theorem Formalism.L2.Th1.F.Taylor.taylor0_inj {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (h : taylor0 f = taylor0 g) : f =ᶠ[nhds 0] g := by sorry
