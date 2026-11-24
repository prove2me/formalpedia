-- Prove2me | Theorems.Thm_Formalism_LT_LTL_near_prod
-- name    : Formalism.LT.LTL.near_prod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:51:55.703824+00:00
-- url     : https://prove2.me/theorems/1361a8f7-cf25-45d3-876c-bc737a17a311
-- title:
--   LTL: near prod
-- statement:
--   The LTL construction uses the near prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L40-L47

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

theorem Formalism.LT.LTL.near_prod {τ : Type*} [DecidableEq ι] {a b : ι → MvPowerSeries τ K}
    (hab : ∀ i, Near 1 (a i) (b i)) (m : ι → ℕ) (s : Finset ι) :
    Near (∑ i ∈ s, m i) (∏ i ∈ s, a i ^ m i) (∏ i ∈ s, b i ^ m i) := by sorry
