-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_tiltedBinomialMass_le_sqrt
-- name    : FirstPassageLinearTransport.exists_tiltedBinomialMass_le_sqrt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:32:29.993904+00:00
-- url     : https://prove2.me/theorems/3dc3acf4-a04f-5457-be12-1ad3a1946043
-- title:
--   First Passage Linear Transport: exists tilted Binomial Mass le sqrt
-- statement:
--   Appendix B.2: uniformly in the atom index, a tilted binomial law with
--   parameter in the Collatz window `(1/2, 2/3)` has mass `O(n⁻¹ʲ²)`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L838-L893
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L838-L893

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.exists_tiltedBinomialMass_le_sqrt
    {p : ℝ} (hpHalf : 1 / 2 < p) (hpTwoThird : p < 2 / 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 0 < n →
      tiltedBinomialMass p n k ≤ C / Real.sqrt n := by sorry
