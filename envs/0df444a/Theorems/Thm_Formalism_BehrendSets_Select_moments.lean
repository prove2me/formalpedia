-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Select_moments
-- name    : Formalism.BehrendSets.Select.moments
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:36:04.646324+00:00
-- url     : https://prove2.me/theorems/7ce06093-23b9-4d87-b705-dd83fb7b7d78
-- title:
--   Select: moments
-- statement:
--   The Select construction uses the moments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/Select.lean#L36-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/Select.lean#L36-L80

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_Select
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
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Select
variable {α : Type} [DecidableEq α]

theorem Formalism.BehrendSets.Select.moments (X : Finset α) (δ : ℝ) :
    (∑ T ∈ X.powerset, wt X δ T * 1 = 1) ∧
    (∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) = δ * X.card) ∧
    (∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) ^ 2 =
      δ * X.card * (1 - δ) + δ ^ 2 * (X.card : ℝ) ^ 2) := by sorry
