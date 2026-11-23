-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_card_le
-- name    : Formalism.CountingSumsFrames.sizeBound_card_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:13.690257+00:00
-- url     : https://prove2.me/theorems/ae7af562-2201-4d42-afb1-eca5c7f49e09
-- title:
--   Counting Sums Frames: size Bound card le
-- statement:
--   The Counting Sums Frames construction uses the size Bound card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L57-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L57-L71

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

theorem Formalism.CountingSumsFrames.sizeBound_card_le (r N Nₛ k Q c' : ℝ) (hr : 2 ≤ r) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hc : 1 ≤ c')
    (hN0 : 0 ≤ N) (hNs2 : Nₛ ≤ 2 * N) : Nₛ ≤ r ^ 2 * N * k * c' * Q ^ 2 := by sorry
