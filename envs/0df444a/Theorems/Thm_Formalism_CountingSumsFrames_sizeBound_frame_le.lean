-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_frame_le
-- name    : Formalism.CountingSumsFrames.sizeBound_frame_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:16.559331+00:00
-- url     : https://prove2.me/theorems/207922b1-a019-43e6-b6be-742d1c40e562
-- title:
--   Counting Sums Frames: size Bound frame le
-- statement:
--   The Counting Sums Frames construction uses the size Bound frame le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L19-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L19-L33

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

theorem Formalism.CountingSumsFrames.sizeBound_frame_le (r N N₁ Nₛ k : ℝ) (hr : 2 ≤ r) (hrN1 : r ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N)
    (hk8 : 8 ≤ k) (hN0 : 0 ≤ N) (hNs1 : Nₛ ≤ N₁) (hNs2 : Nₛ ≤ 2 * N) :
    Nₛ * (N₁ + r * k) ≤ 2 * r ^ 2 * N * k := by sorry
