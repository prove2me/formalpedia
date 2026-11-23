-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Rand_wt_union
-- name    : Formalism.BehrendSets.Rand.wt_union
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:47.144668+00:00
-- url     : https://prove2.me/theorems/baed0999-c538-474a-b6c9-601f3b56aa3b
-- title:
--   Rand: wt union
-- statement:
--   The Rand construction uses the wt union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L38-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L38-L49

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

theorem Formalism.BehrendSets.Rand.wt_union (X S U : Finset α) (δ : ℝ) (hU : U ⊆ X \ S) :
    wt X δ (S ∪ U) = δ ^ S.card * wt (X \ S) δ U := by sorry
