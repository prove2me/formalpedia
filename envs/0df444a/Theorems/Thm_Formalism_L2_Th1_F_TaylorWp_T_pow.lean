-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_pow
-- name    : Formalism.L2.Th1.F.TaylorWp.T.pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:08.790175+00:00
-- url     : https://prove2.me/theorems/28ccfb1b-215e-41ee-9243-c0a91dd26041
-- title:
--   T: pow
-- statement:
--   The T construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorWp.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorWp.lean#L28-L32

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_pow

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

theorem Formalism.L2.Th1.F.TaylorWp.T.pow (hr : TaylorRing) {f : ℂ → ℂ} {F : PowerSeries ℂ} (hf : T f F) (k : ℕ) :
    T (fun z => f z ^ k) (F ^ k) := by sorry
