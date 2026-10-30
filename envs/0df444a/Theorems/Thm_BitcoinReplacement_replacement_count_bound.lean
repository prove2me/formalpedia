-- Prove2me | Theorems.Thm_BitcoinReplacement_replacement_count_bound
-- name    : BitcoinReplacement.replacement_count_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:08:56.666993+00:00
-- url     : https://prove2.me/theorems/f63b715a-5563-4037-90be-54a182720bc3
-- title:
--   The number of replacements is bounded by the fee gained
-- statement:
--   For a chain of $n$ replacements: $t_0.\text{fee} + n \cdot \text{getFee}(1) \le t_n.\text{fee}$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.replacement_count_bound (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee + Rs.length * rate.getFee 1 ≤ (BitcoinReplacement.chainEnd t₀ Rs).fee := by sorry
