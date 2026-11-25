-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lcssyt_colExp_sum_ge
-- name    : Formalism.GradedWeylDivisibility.lcssyt_colExp_sum_ge
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:38:09.628496+00:00
-- url     : https://prove2.me/theorems/66a75cba-6d6d-4c36-863f-102be6570624
-- title:
--   Graded Weyl Divisibility: lcssyt col Exp sum ge
-- statement:
--   The Graded Weyl Divisibility construction uses the lcssyt col Exp sum ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCssytLemmas.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCssytLemmas.lean#L69-L71

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCssytLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.lcssyt_colExp_sum_ge {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (S : Finset (Fin r)) (t : Fin n)
    (ht : ¬ t.val < h) : ∑ b ∈ S, colExp c hh (b, t) = 0 := by sorry
