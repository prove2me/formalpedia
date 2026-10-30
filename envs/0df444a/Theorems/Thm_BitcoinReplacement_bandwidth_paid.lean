-- Prove2me | Theorems.Thm_BitcoinReplacement_bandwidth_paid
-- name    : BitcoinReplacement.bandwidth_paid
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:06:13.766056+00:00
-- url     : https://prove2.me/theorems/9608526f-67bb-4641-b5cf-3507d1ef342b
-- title:
--   No free relay: a chain of replacements pays the incremental fee for every byte it relayed
-- statement:
--   For any rate, any $t_0$ and any chain `IsChain rate t₀ Rs` of $n$ replacements with new transactions $t_1, \dots, t_n$: $t_0.\text{fee} + \sum_{i=1}^{n} \text{getFee}(\text{vsize } t_i) \le t_n.\text{fee}$. The final transaction's fee covers the original fee plus the incremental relay fee of every replacement relayed along the way, in Core's own rounded-up `GetFee`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.bandwidth_paid (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee + ((BitcoinReplacement.chainVsizes Rs).map rate.getFee).sum ≤
      (BitcoinReplacement.chainEnd t₀ Rs).fee := by sorry
