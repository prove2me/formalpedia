-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Rand_prob_filter
-- name    : Formalism.BehrendSets.Rand.prob_filter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:59.352882+00:00
-- url     : https://prove2.me/theorems/531f03cd-d3f0-4b16-86f8-138191d95088
-- title:
--   Rand: prob filter
-- statement:
--   The Rand construction uses the prob filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L21-L23

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

theorem Formalism.BehrendSets.Rand.prob_filter (X : Finset α) (δ : ℝ) (P : Finset α → Prop) [DecidablePred P] :
    prob X δ P = ∑ T ∈ X.powerset.filter P, wt X δ T := by sorry
