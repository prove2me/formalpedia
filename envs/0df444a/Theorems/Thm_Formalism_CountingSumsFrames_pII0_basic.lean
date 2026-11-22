-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_pII0_basic
-- name    : Formalism.CountingSumsFrames.pII0_basic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:46.247237+00:00
-- url     : https://prove2.me/theorems/330e46e2-774b-4591-b67c-d36b16b15a37
-- title:
--   Counting Sums Frames: p II0 basic
-- statement:
--   The Counting Sums Frames construction uses the p II0 basic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L12-L17

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

theorem Formalism.CountingSumsFrames.pII0_basic (r N N₁ k : ℝ) (hr : 2 ≤ r) (hrN1 : r ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N)
    (hk : N₁ + 3 * r ≤ k) : r ≤ N ∧ 8 ≤ k ∧ N₁ + 1 ≤ 2 * r * N := by sorry
