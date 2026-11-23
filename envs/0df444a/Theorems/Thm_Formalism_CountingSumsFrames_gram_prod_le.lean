-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_gram_prod_le
-- name    : Formalism.CountingSumsFrames.gram_prod_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:47:18.918496+00:00
-- url     : https://prove2.me/theorems/0aa2ae2b-9464-4287-a269-232938566258
-- title:
--   Counting Sums Frames: gram prod le
-- statement:
--   The Counting Sums Frames construction uses the gram prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FrameMultinomialBoundHolds.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FrameMultinomialBoundHolds.lean#L49-L54

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrameMultinomialBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Real
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.gram_prod_le (m : ℕ) (f g : Fin m → ℝ) (t : ℝ) (hf : ∀ j, 0 ≤ f j)
    (hfg : ∀ j, f j ≤ (1 + t) * g j) :
    ∏ j, f j ≤ (1 + t) ^ m * ∏ j, g j := by sorry
