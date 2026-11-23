-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_slackBound_coeff
-- name    : Formalism.CountingSumsFrames.slackBound_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:16.465488+00:00
-- url     : https://prove2.me/theorems/e9acdd50-e42e-43a3-9008-c65a99578b06
-- title:
--   Counting Sums Frames: slack Bound coeff
-- statement:
--   The Counting Sums Frames construction uses the slack Bound coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSlackBoundsHolds.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSlackBoundsHolds.lean#L16-L24

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

theorem Formalism.CountingSumsFrames.slackBound_coeff {M P B c : ℝ} (hM : 0 < M) (hc : 0 < c) (hB : 0 ≤ B) (hP : 16 * c * M ≤ P) :
    c * P⁻¹ * B ≤ B / M / 2 / 8 := by sorry
