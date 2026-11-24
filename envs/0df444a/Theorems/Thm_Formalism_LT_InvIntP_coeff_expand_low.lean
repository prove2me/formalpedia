-- Prove2me | Theorems.Thm_Formalism_LT_InvIntP_coeff_expand_low
-- name    : Formalism.LT.InvIntP.coeff_expand_low
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:50:51.537296+00:00
-- url     : https://prove2.me/theorems/7acb0423-abf3-4477-826e-5482d045a4b6
-- title:
--   Inv Int P: coeff expand low
-- statement:
--   The Inv Int P construction uses the coeff expand low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L102-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L102-L122

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT Formalism.LT.InvIntP
open Formalism.G Formalism.G.LogCR

theorem Formalism.LT.InvIntP.coeff_expand_low {K : Type u} [NormedField K] {ι : Type v} (q : ℕ) (hq : q ≠ 0)
    (hq2 : 2 ≤ q) (σ : K →+* K) (D : MvPowerSeries ι K) (N : ℕ) (hN : 1 ≤ N)
    (hlow : ∀ d : ι →₀ ℕ, d.degree < N → MvPowerSeries.coeff d D = 0)
    (d : ι →₀ ℕ) (hd : d.degree = N) :
    MvPowerSeries.coeff d (MvPowerSeries.expand q hq (MvPowerSeries.map σ D)) = 0 := by sorry
