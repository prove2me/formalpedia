-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Rand_wt_nonneg
-- name    : Formalism.BehrendSets.Rand.wt_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:02.365805+00:00
-- url     : https://prove2.me/theorems/5b2f4cc3-02fb-4659-a024-0657ee6387e9
-- title:
--   Rand: wt nonneg
-- statement:
--   The Rand construction uses the wt nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/ProbEqSumIte.lean#L25-L27

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

theorem Formalism.BehrendSets.Rand.wt_nonneg (X T : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) : 0 ≤ wt X δ T := by sorry
