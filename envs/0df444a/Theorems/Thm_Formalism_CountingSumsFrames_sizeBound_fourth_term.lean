-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_fourth_term
-- name    : Formalism.CountingSumsFrames.sizeBound_fourth_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:21.793193+00:00
-- url     : https://prove2.me/theorems/c30ba8a2-d73a-4dd7-a009-a7c83ae1fc02
-- title:
--   Counting Sums Frames: size Bound fourth term
-- statement:
--   The Counting Sums Frames construction uses the size Bound fourth term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L182-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L182-L191

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSizeBoundsHolds
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

theorem Formalism.CountingSumsFrames.sizeBound_fourth_term (r N k Q c' Y : ℝ) (hr : 1 ≤ r) (hN : 1 ≤ N) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (hc : 1 ≤ c') (hY : 0 ≤ Y) : Y * k ^ 2 * Q ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by sorry
