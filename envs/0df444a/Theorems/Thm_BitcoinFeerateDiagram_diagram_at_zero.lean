-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_diagram_at_zero
-- name    : BitcoinFeerateDiagram.diagram_at_zero
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:56:44.634849+00:00
-- url     : https://prove2.me/theorems/3e0859fb-9994-427c-a2c9-d2fe8bff52e8
-- title:
--   The diagram starts at the origin
-- statement:
--   For positive chunk sizes: `diagram cs 0 = 0`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.diagram_at_zero {cs : List FeeFrac} (h : SizesPos cs) :
    diagram cs 0 = 0 := by sorry
