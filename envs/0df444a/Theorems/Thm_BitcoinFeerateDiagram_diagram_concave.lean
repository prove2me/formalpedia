-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_diagram_concave
-- name    : BitcoinFeerateDiagram.diagram_concave
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:58:08.397222+00:00
-- url     : https://prove2.me/theorems/cc3aee1c-5f3d-4be4-bfae-e35afc96f057
-- title:
--   A chunking with non-increasing feerates has a concave diagram
-- statement:
--   For positive sizes and non-increasing feerates, `diagram cs` is concave on $[0, \text{diagramSize}]$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.diagram_concave (cs : List FeeFrac) (hpos : SizesPos cs)
    (hsort : FeeratesNonIncreasing cs) :
    ConcaveOn ℚ (Set.Icc 0 (diagramSize cs : ℚ)) (diagram cs) := by sorry
