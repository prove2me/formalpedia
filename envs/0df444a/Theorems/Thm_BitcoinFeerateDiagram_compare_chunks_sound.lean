-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_compare_chunks_sound
-- name    : BitcoinFeerateDiagram.compare_chunks_sound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:57:07.836308+00:00
-- url     : https://prove2.me/theorems/e5e1a6a1-c4b8-441b-94ea-61dc68cb1a05
-- title:
--   Core's CompareChunks sweep decides the pointwise comparison of the two feerate diagrams
-- statement:
--   For chunk lists with positive sizes: `compareChunks c0 c1` is `greater` iff `StrictlyBetter c0 c1` (never below, strictly above somewhere); `less` iff `StrictlyBetter c1 c0`; `equivalent` iff the diagrams are equal on $[0, \infty)$; `unordered` iff each is strictly above the other somewhere. The C++ sweep over breakpoints computes exactly the mathematical comparison of the two piecewise-linear functions; sorted feerates are not needed.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.compare_chunks_sound (c0 c1 : List FeeFrac) (h0 : SizesPos c0)
    (h1 : SizesPos c1) :
    (compareChunks c0 c1 = .greater ↔ StrictlyBetter c0 c1) ∧
    (compareChunks c0 c1 = .less ↔ StrictlyBetter c1 c0) ∧
    (compareChunks c0 c1 = .equivalent ↔ ∀ x : ℚ, 0 ≤ x → diagram c0 x = diagram c1 x) ∧
    (compareChunks c0 c1 = .unordered ↔ BetterSomewhere c0 c1 ∧ BetterSomewhere c1 c0) := by sorry
