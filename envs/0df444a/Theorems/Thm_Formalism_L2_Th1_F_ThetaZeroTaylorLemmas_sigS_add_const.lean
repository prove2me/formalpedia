-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_sigS_add_const
-- name    : Formalism.L2.Th1.F.ThetaZeroTaylorLemmas.sigS_add_const
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:29:22.558436+00:00
-- url     : https://prove2.me/theorems/f17cd867-6ea6-47c8-9935-cbe1ab04ba75
-- title:
--   Theta Zero Taylor Lemmas: sig S add const
-- statement:
--   The Theta Zero Taylor Lemmas construction uses the sig S add const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorEvenTheta.lean#L19-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorEvenTheta.lean#L19-L37

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorEvenTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.ThetaZeroTaylorLemmas
open PowerSeries

theorem Formalism.L2.Th1.F.ThetaZeroTaylorLemmas.sigS_add_const (Q : PowerSeries ℂ) (s : ℂ) :
    B.sigS (Q + C s) = -B.prim (B.prim Q) + -(C (s / 2) * X ^ 2) := by sorry
