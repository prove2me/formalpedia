-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_no_free_relay_diagram
-- name    : BitcoinFeerateDiagram.no_free_relay_diagram
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:59:20.640193+00:00
-- url     : https://prove2.me/theorems/724b39a2-6ae4-4257-bb3d-da6326d1ffb5
-- title:
--   No free relay under the cluster-mempool rules
-- statement:
--   If the old and new diagrams' totals are a common $F$ plus the evicted fees and plus the replacement's fee, and both `ImprovesFeerateDiagram` and the replacement mission's `PaysForRBF rate R` hold: the new diagram is strictly better and its total fee exceeds the old by at least `rate.getFee R.new.vsize`. The replacement mission's no-free-relay theorems therefore hold at the pinned revision's actual rules.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.no_free_relay_diagram (rate : FeeRate) (R : Replacement)
    (old new : List FeeFrac) (F : ℤ) (hold : SizesPos old) (hnew : SizesPos new)
    (hfold : diagramFee old = F + totalFee R.evicted) (hfnew : diagramFee new = F + R.new.fee)
    (himp : ImprovesFeerateDiagram old new) (hpay : PaysForRBF rate R) :
    StrictlyBetter new old ∧ diagramFee old + rate.getFee R.new.vsize ≤ diagramFee new := by sorry
