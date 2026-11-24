-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_prod_one_sub_inv_ge_inv_card_succ
-- name    : Formalism.ZeroFreeDirichlet.prod_one_sub_inv_ge_inv_card_succ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:44:12.648452+00:00
-- url     : https://prove2.me/theorems/462c93fa-bbaf-45f4-8163-0f6ae88db49a
-- title:
--   Zero Free Dirichlet: prod one sub inv ge inv card succ
-- statement:
--   The Zero Free Dirichlet construction uses the prod one sub inv ge inv card succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SameCharacterLFunctionOne.lean#L9-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SameCharacterLFunctionOne.lean#L9-L42

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SameCharacterLFunctionOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.prod_one_sub_inv_ge_inv_card_succ (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    1 / ((S.card : ℝ) + 1) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by sorry
