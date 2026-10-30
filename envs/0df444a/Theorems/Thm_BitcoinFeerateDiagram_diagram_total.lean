-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_diagram_total
-- name    : BitcoinFeerateDiagram.diagram_total
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:56:20.334077+00:00
-- url     : https://prove2.me/theorems/6bc91462-0817-4ac0-8ebd-1d7886d6644f
-- title:
--   Past its total size the diagram is the total fee
-- statement:
--   For positive chunk sizes and $x \ge$ `diagramSize cs`: `diagram cs x = diagramFee cs`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.diagram_total {cs : List FeeFrac} (h : SizesPos cs) {x : ℚ}
    (hx : (diagramSize cs : ℚ) ≤ x) : diagram cs x = diagramFee cs := by sorry
