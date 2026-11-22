-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Rand_prob_eq_sum_ite
-- name    : Formalism.BehrendSets.Rand.prob_eq_sum_ite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:48.512272+00:00
-- url     : https://prove2.me/theorems/390e91f6-a889-4263-893a-b290d49b1f2a
-- title:
--   Rand: prob eq sum ite
-- statement:
--   The Rand construction uses the prob eq sum ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L12-L19

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

theorem Formalism.BehrendSets.Rand.prob_eq_sum_ite (X : Finset α) (δ : ℝ) (P : Finset α → Prop) [DecidablePred P] :
    prob X δ P = ∑ T ∈ X.powerset, if P T then wt X δ T else 0 := by sorry
