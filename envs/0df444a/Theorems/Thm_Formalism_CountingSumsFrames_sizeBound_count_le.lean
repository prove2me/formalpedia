-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_count_le
-- name    : Formalism.CountingSumsFrames.sizeBound_count_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:09.859802+00:00
-- url     : https://prove2.me/theorems/2ca58baf-1559-4e97-bd69-e6175e74389a
-- title:
--   Counting Sums Frames: size Bound count le
-- statement:
--   The Counting Sums Frames construction uses the size Bound count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L49-L55

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

theorem Formalism.CountingSumsFrames.sizeBound_count_le (r N N₁ Nₛ : ℝ) (hrN1 : 2 ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N) (hNs1 : Nₛ ≤ N₁) :
    Nₛ * (N₁ + 1) ≤ 2 * r * N := by sorry
