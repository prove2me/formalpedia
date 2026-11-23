-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_slack_ge_half
-- name    : Formalism.CountingSumsFrames.slack_ge_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:38.27773+00:00
-- url     : https://prove2.me/theorems/21d66ca1-eb90-4259-bac9-bbd459c83fa5
-- title:
--   Counting Sums Frames: slack ge half
-- statement:
--   The Counting Sums Frames construction uses the slack ge half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSlackBoundsHolds.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSlackBoundsHolds.lean#L9-L14

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSlackBoundsHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CountingSumsFrames
open Real

theorem Formalism.CountingSumsFrames.slack_ge_half {Y B : ℝ} {k : ℕ} (hM : 0 < Y * (k : ℝ) ^ 2) (hB : 2 * (Y * (k : ℝ) ^ 2) ≤ B) :
    B / (Y * (k : ℝ) ^ 2) / 2 ≤ slII Y k B := by sorry
