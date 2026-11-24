-- Prove2me | Theorems.Thm_Formalism_LT_LTL_cong_monomial
-- name    : Formalism.LT.LTL.cong_monomial
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:50:51.784681+00:00
-- url     : https://prove2.me/theorems/25058835-a05c-44ec-a2b3-7cf44548cf2b
-- title:
--   LTL: cong monomial
-- statement:
--   The LTL construction uses the cong monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L237-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L237-L246

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

theorem Formalism.LT.LTL.cong_monomial {τ : Type*} {c : K} {a b : ι → MvPowerSeries τ K}
    (hab : ∀ i, Cong c (a i) (b i)) (m : ι →₀ ℕ) :
    Cong c (m.prod fun s e => a s ^ e) (m.prod fun s e => b s ^ e) := by sorry
