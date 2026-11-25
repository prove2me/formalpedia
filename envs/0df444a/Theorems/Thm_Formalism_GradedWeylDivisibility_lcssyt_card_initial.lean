-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lcssyt_card_initial
-- name    : Formalism.GradedWeylDivisibility.lcssyt_card_initial
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:35:43.207653+00:00
-- url     : https://prove2.me/theorems/9b1c24b5-93b2-4a10-9a0a-065e36d52bff
-- title:
--   Graded Weyl Divisibility: lcssyt card initial
-- statement:
--   The Graded Weyl Divisibility construction uses the lcssyt card initial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCssytLemmas.lean#L9-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCssytLemmas.lean#L9-L32

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

theorem Formalism.GradedWeylDivisibility.lcssyt_card_initial {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ t t' : Fin n, t' ≤ t → P t → P t') (t : Fin n) :
    t.val < (univ.filter P).card ↔ P t := by sorry
