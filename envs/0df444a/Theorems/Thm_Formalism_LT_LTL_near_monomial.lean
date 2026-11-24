-- Prove2me | Theorems.Thm_Formalism_LT_LTL_near_monomial
-- name    : Formalism.LT.LTL.near_monomial
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:51:12.68337+00:00
-- url     : https://prove2.me/theorems/c86584cd-08ff-4485-9f60-60e5f3ec66a2
-- title:
--   LTL: near monomial
-- statement:
--   The LTL construction uses the near monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L49-L54

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
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
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] {ι : Type*}

theorem Formalism.LT.LTL.near_monomial {τ : Type*} {a b : ι → MvPowerSeries τ K}
    (hab : ∀ i, Near 1 (a i) (b i)) (m : ι →₀ ℕ) :
    Near m.degree (m.prod fun s e => a s ^ e) (m.prod fun s e => b s ^ e) := by sorry
