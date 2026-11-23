-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_factProd_ne_zero
-- name    : Formalism.CountingSumsFrames.factProd_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:13.674869+00:00
-- url     : https://prove2.me/theorems/1b2dbc24-0183-4b48-b502-f2f4e83ec3f9
-- title:
--   Counting Sums Frames: fact Prod ne zero
-- statement:
--   The Counting Sums Frames construction uses the fact Prod ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L65-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L65-L65

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.factProd_ne_zero {σ : Type} [Fintype σ] (α : σ →₀ ℕ) : factProd α ≠ 0 := by sorry
