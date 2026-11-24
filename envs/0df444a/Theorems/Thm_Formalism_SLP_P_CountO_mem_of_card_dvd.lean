-- Prove2me | Theorems.Thm_Formalism_SLP_P_CountO_mem_of_card_dvd
-- name    : Formalism.SLP.P.CountO.mem_of_card_dvd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:29:14.945828+00:00
-- url     : https://prove2.me/theorems/12766331-d9aa-47eb-ae7b-930e3b4fa0db
-- title:
--   Count O: mem of card dvd
-- statement:
--   The Count O construction uses the mem of card dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/CountO.lean#L397-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/CountO.lean#L397-L418

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
open NumberField
variable (E : Type) [Field E] [NumberField E]
variable {E}

theorem Formalism.SLP.P.CountO.mem_of_card_dvd {P : Ideal (𝓞 E)} [P.IsMaximal] {p e : ℕ}
    (h : Nat.card (𝓞 E ⧸ P) ∣ p ^ e) : ((p : ℕ) : 𝓞 E) ∈ P := by sorry
