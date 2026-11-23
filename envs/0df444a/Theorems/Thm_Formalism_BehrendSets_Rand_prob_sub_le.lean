-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Rand_prob_sub_le
-- name    : Formalism.BehrendSets.Rand.prob_sub_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:40.438291+00:00
-- url     : https://prove2.me/theorems/4f5c4abd-5f6d-419f-83a2-c9077586c8d5
-- title:
--   Rand: prob sub le
-- statement:
--   The Rand construction uses the prob sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L89-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L89-L98

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

theorem Formalism.BehrendSets.Rand.prob_sub_le (X S : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) :
    prob X δ (fun T => S ⊆ T) ≤ δ ^ S.card := by sorry
