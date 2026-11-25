-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_one_le_product
-- name    : Formalism.CountingSumsFrames.sizeBound_one_le_product
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:24:46.049318+00:00
-- url     : https://prove2.me/theorems/f8100c35-a1d3-40eb-bde0-ef677ca59647
-- title:
--   Counting Sums Frames: size Bound one le product
-- statement:
--   The Counting Sums Frames construction uses the size Bound one le product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L235-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L235-L241

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

theorem Formalism.CountingSumsFrames.sizeBound_one_le_product (k r N Q c' Y : ℝ) (hk : 1 ≤ k) (hr : 1 ≤ r) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hc : 1 ≤ c') (hY : 1 ≤ Y) : 1 ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by sorry
