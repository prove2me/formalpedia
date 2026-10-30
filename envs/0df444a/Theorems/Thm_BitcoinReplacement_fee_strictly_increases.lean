-- Prove2me | Theorems.Thm_BitcoinReplacement_fee_strictly_increases
-- name    : BitcoinReplacement.fee_strictly_increases
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:05:43.02085+00:00
-- url     : https://prove2.me/theorems/46513f82-81c7-432f-8f1f-6f207c48cdae
-- title:
--   Every evicted transaction paid strictly less than its replacement
-- statement:
--   For a rate with positive numerator, a valid replacement $R$ and any $t \in$ `R.evicted`: `t.fee < R.new.fee`. With a zero incremental relay fee the inequality can be an equality, hence the hypothesis.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.fee_strictly_increases (rate : BitcoinReplacement.FeeRate)
    (hr : 0 < rate.fee) (R : BitcoinReplacement.Replacement)
    (hR : BitcoinReplacement.Valid rate R) (t : BitcoinReplacement.Tx) (ht : t ∈ R.evicted) :
    t.fee < R.new.fee := by sorry
