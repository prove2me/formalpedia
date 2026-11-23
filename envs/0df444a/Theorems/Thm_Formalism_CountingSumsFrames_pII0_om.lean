-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_pII0_om
-- name    : Formalism.CountingSumsFrames.pII0_om
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:44.580852+00:00
-- url     : https://prove2.me/theorems/3fe471c9-fad1-4c8c-a52e-25ea3dd6a395
-- title:
--   Counting Sums Frames: p II0 om
-- statement:
--   The Counting Sums Frames construction uses the p II0 om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L243-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L243-L250

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

theorem Formalism.CountingSumsFrames.pII0_om (r N n' c₀ c'' : ℕ) (hr : 1 ≤ r) (hN : 1 ≤ N) : (c₀ : ℝ) ≤ omII r N n' c₀ c'' := by sorry
