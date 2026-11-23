-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_fock_log_le
-- name    : Formalism.CountingSumsFrames.fock_log_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:39.505709+00:00
-- url     : https://prove2.me/theorems/458e6c36-b7a2-48e3-8b7c-132e3d9fe070
-- title:
--   Counting Sums Frames: fock log le
-- statement:
--   The Counting Sums Frames construction uses the fock log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L49-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L49-L63

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

theorem Formalism.CountingSumsFrames.fock_log_le (p : ℕ) [hp : Fact p.Prime] (k D : ℕ) (a : ℝ) (ha : 0 ≤ a) (hk : 1 ≤ k)
    (hD : (D : ℝ) ≤ 2 * a) : (Nat.log p D : ℝ) ≤ Real.logb p (2 * a + k) + 1 := by sorry
