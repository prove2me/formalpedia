-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_eq_one_of_sub_one_mem
-- name    : Formalism.TwoAdicCyclotomicDecomposition.odd_eq_one_of_sub_one_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:30:51.8938+00:00
-- url     : https://prove2.me/theorems/f9404b94-c9a8-415c-96b1-4ec912ef8a14
-- title:
--   Two Adic Cyclotomic Decomposition: odd eq one of sub one mem
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the odd eq one of sub one mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L69-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L69-L81

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.odd_eq_one_of_sub_one_mem {S : Type*} [CommRing S] [IsDomain S] (P : Ideal S) {η : S}
    {m : ℕ} (hη : η ^ m = 1) (hm : (m : S) ∉ P) (h : η - 1 ∈ P) : η = 1 := by sorry
