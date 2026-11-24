-- Prove2me | Theorems.Thm_Formalism_LT_ExpP_scalar_bound
-- name    : Formalism.LT.ExpP.scalar_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:51:20.032801+00:00
-- url     : https://prove2.me/theorems/2c898a0f-0acc-4259-b548-f70859d9d57d
-- title:
--   Exp P: scalar bound
-- statement:
--   The Exp P construction uses the scalar bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormNatCastOfNotDvd.lean#L79-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormNatCastOfNotDvd.lean#L79-L124

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
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
universe u
open Formalism Formalism.LT Formalism.LT.ExpP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.ExpP.scalar_bound {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (c : K) (d m : ℕ) (hmd : m < d)
    (hc : ‖(d : K) * c‖ ≤ 1) :
    ‖c * ((p : K) ^ (d - m) * (d.choose m : K))‖ ≤ ‖(p : K)‖ := by sorry
