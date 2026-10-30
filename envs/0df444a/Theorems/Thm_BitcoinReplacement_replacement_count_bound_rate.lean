-- Prove2me | Theorems.Thm_BitcoinReplacement_replacement_count_bound_rate
-- name    : BitcoinReplacement.replacement_count_bound_rate
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:10:00.414319+00:00
-- url     : https://prove2.me/theorems/7be85bc9-bf75-44df-82ee-ac5557883f63
-- title:
--   Replacements per satoshi: n ≤ (fee gained)/rate
-- statement:
--   For a chain of $n$ replacements: $n \cdot \text{fee} \le (t_n.\text{fee} - t_0.\text{fee}) \cdot \text{size}$, i.e. $n \le (t_n.\text{fee} - t_0.\text{fee}) / r$ with $r$ the rate in sat/vB.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.replacement_count_bound_rate (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    Rs.length * rate.fee ≤ ((BitcoinReplacement.chainEnd t₀ Rs).fee - t₀.fee) * rate.size := by sorry
