-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Select_step
-- name    : Formalism.BehrendSets.Select.step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:58.182597+00:00
-- url     : https://prove2.me/theorems/6df653c0-b5d9-44fa-853d-53d4051356be
-- title:
--   Select: step
-- statement:
--   The Select construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/Select.lean#L16-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/Select.lean#L16-L34

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

theorem Formalism.BehrendSets.Select.step (X : Finset α) (δ : ℝ) {a : α} (ha : a ∉ X) (g : Finset α → ℝ) :
    ∑ T ∈ (insert a X).powerset, wt (insert a X) δ T * g T =
      ∑ T ∈ X.powerset, wt X δ T * ((1 - δ) * g T + δ * g (insert a T)) := by sorry
