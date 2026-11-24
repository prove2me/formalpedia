-- Prove2me | Theorems.Thm_Formalism_LT_InvIntP_funEqLowCoeff
-- name    : Formalism.LT.InvIntP.funEqLowCoeff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:50:54.94905+00:00
-- url     : https://prove2.me/theorems/c273a13b-83e4-49fe-a73b-acedcbfe2346
-- title:
--   Inv Int P: fun Eq Low Coeff
-- statement:
--   The Inv Int P construction uses the fun Eq Low Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L124-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L124-L129

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

theorem Formalism.LT.InvIntP.funEqLowCoeff {K : Type u} [NormedField K] {ι : Type v} (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K) (hq2 : 2 ≤ q) (D : MvPowerSeries ι K) (hD : IsFunEqTypeMv p q hq σ D)
    (N : ℕ) (hN : 1 ≤ N) (hlow : ∀ d : ι →₀ ℕ, d.degree < N → MvPowerSeries.coeff d D = 0)
    (d : ι →₀ ℕ) (hd : d.degree = N) : ‖MvPowerSeries.coeff d D‖ ≤ 1 := by sorry
