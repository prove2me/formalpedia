-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_pII0_floor
-- name    : Formalism.CountingSumsFrames.pII0_floor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:34.991195+00:00
-- url     : https://prove2.me/theorems/bfe404bb-f405-4c41-be1b-b3ac1451703f
-- title:
--   Counting Sums Frames: p II0 floor
-- statement:
--   The Counting Sums Frames construction uses the p II0 floor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L219-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L219-L233

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

theorem Formalism.CountingSumsFrames.pII0_floor (L Y k Q a B : ℝ) (hQ0 : 0 < Q) (ha : 0 ≤ a) (hYk100 : 100 ≤ Y * k ^ 2)
    (h : (L + 1) * (Y * k ^ 2 * Q) ≤ a) (hB : a / Q ≤ B) :
    L ≤ ((⌊B / (Y * k ^ 2)⌋ : ℤ) : ℝ) ∧ ((⌊B / (Y * k ^ 2)⌋ : ℤ) : ℝ) ≤ B / 100 := by sorry
