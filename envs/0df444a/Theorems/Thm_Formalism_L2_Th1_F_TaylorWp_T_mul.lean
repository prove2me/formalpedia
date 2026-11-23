-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
-- name    : Formalism.L2.Th1.F.TaylorWp.T.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:43.513555+00:00
-- url     : https://prove2.me/theorems/13761492-728a-454e-843d-22d4514eef02
-- title:
--   T: mul
-- statement:
--   The T construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorWp.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorWp.lean#L18-L20

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul

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
open Formalism.L2.Th1.F.TaylorWp

theorem Formalism.L2.Th1.F.TaylorWp.T.mul (hr : TaylorRing) {f g : ℂ → ℂ} {F G : PowerSeries ℂ} (hf : T f F) (hg : T g G) :
    T (fun z => f z * g z) (F * G) := by sorry
