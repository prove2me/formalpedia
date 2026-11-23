-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Rand_prob_exists_le
-- name    : Formalism.BehrendSets.Rand.prob_exists_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:44.572054+00:00
-- url     : https://prove2.me/theorems/77041fa0-23c9-4f54-b0f1-9ad645e3e794
-- title:
--   Rand: prob exists le
-- statement:
--   The Rand construction uses the prob exists le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L111-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L111-L131

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

theorem Formalism.BehrendSets.Rand.prob_exists_le {ι : Type} (X : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1)
    (J : Finset ι) (E : ι → Finset α → Prop) :
    prob X δ (fun T => ∃ j ∈ J, E j T) ≤ ∑ j ∈ J, prob X δ (E j) := by sorry
