-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_improvesFeerateDiagram_iff
-- name    : BitcoinFeerateDiagram.improvesFeerateDiagram_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:57:27.250368+00:00
-- url     : https://prove2.me/theorems/cb21291a-09c7-4457-aaba-00d8a856e219
-- title:
--   ImprovesFeerateDiagram means a strictly better diagram
-- statement:
--   For positive sizes: `ImprovesFeerateDiagram old new ↔ StrictlyBetter new old`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.improvesFeerateDiagram_iff (old new : List FeeFrac)
    (hold : SizesPos old) (hnew : SizesPos new) :
    ImprovesFeerateDiagram old new ↔ StrictlyBetter new old := by sorry
