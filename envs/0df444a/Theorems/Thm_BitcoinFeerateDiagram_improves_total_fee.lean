-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_improves_total_fee
-- name    : BitcoinFeerateDiagram.improves_total_fee
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:58:30.286634+00:00
-- url     : https://prove2.me/theorems/2139b05b-9d46-43ae-83e1-561683e62d82
-- title:
--   A strict improvement does not lower the total fee
-- statement:
--   For positive sizes: `ImprovesFeerateDiagram old new → diagramFee old ≤ diagramFee new`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.improves_total_fee (old new : List FeeFrac) (hold : SizesPos old)
    (hnew : SizesPos new) (h : ImprovesFeerateDiagram old new) :
    diagramFee old ≤ diagramFee new := by sorry
