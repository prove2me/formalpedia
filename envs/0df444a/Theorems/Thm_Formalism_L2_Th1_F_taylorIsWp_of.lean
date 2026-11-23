-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_taylorIsWp_of
-- name    : Formalism.L2.Th1.F.taylorIsWp_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:50.619914+00:00
-- url     : https://prove2.me/theorems/56712031-6d27-4d61-9207-713c6b385327
-- title:
--   F: taylor Is Wp of
-- statement:
--   The F construction uses the taylor Is Wp of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorWp.lean#L49-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorWp.lean#L49-L85

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

theorem Formalism.L2.Th1.F.taylorIsWp_of (hr : TaylorRing) (hd : TaylorDeriv) : TaylorIsWp := by sorry
