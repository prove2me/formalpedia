-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Select_variance
-- name    : Formalism.BehrendSets.Select.variance
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:04.094101+00:00
-- url     : https://prove2.me/theorems/b4daa7a9-63fb-4b38-a501-55c4569a3464
-- title:
--   Select: variance
-- statement:
--   The Select construction uses the variance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/Select.lean#L82-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/Select.lean#L82-L94

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

theorem Formalism.BehrendSets.Select.variance (X : Finset α) (δ : ℝ) :
    ∑ T ∈ X.powerset, wt X δ T * ((T.card : ℝ) - δ * X.card) ^ 2 = δ * X.card * (1 - δ) := by sorry
