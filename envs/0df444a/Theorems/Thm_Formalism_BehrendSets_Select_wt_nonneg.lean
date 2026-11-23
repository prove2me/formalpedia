-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Select_wt_nonneg
-- name    : Formalism.BehrendSets.Select.wt_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:05.162577+00:00
-- url     : https://prove2.me/theorems/729fa1c6-5122-4e5d-8a91-10a6cb34fd2d
-- title:
--   Select: wt nonneg
-- statement:
--   The Select construction uses the wt nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/Select.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/Select.lean#L12-L14

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

theorem Formalism.BehrendSets.Select.wt_nonneg (X : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (T : Finset α) :
    0 ≤ wt X δ T := by sorry
