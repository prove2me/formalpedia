-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Rand_expect_sum_ite
-- name    : Formalism.BehrendSets.Rand.expect_sum_ite
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:19:48.458119+00:00
-- url     : https://prove2.me/theorems/0e8f9df8-b801-52ca-a3d9-bbb9560f7ac6
-- title:
--   Rand: expect sum ite
-- statement:
--   The Rand construction uses the expect sum ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L198-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L198-L212

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Rand
variable {α : Type} [DecidableEq α]

theorem Formalism.BehrendSets.Rand.expect_sum_ite {ι : Type} (X : Finset α) (δ : ℝ) (I : Finset ι) (c : ι → ℝ)
    (E : ι → Finset α → Prop) (dec : ∀ i, DecidablePred (E i)) :
    expect X δ (fun T => ∑ i ∈ I, c i * (if E i T then 1 else 0))
      = ∑ i ∈ I, c i * prob X δ (E i) := by sorry
