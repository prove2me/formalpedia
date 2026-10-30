-- Prove2me | Theorems.Thm_BitcoinReplacement_bandwidth_paid_rate
-- name    : BitcoinReplacement.bandwidth_paid_rate
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:07:28.22664+00:00
-- url     : https://prove2.me/theorems/bfe2ea1d-f978-4778-b9a7-ee342f4c8fce
-- title:
--   No free relay, exact integer form
-- statement:
--   Under the same hypotheses: $t_0.\text{fee} \cdot \text{size} + \text{fee} \cdot \sum_i \text{vsize } t_i \le t_n.\text{fee} \cdot \text{size}$, where the rate is fee/size; no rounding is lost because `getFee` rounds up.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.bandwidth_paid_rate (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee * rate.size + rate.fee * (BitcoinReplacement.chainVsizes Rs).sum ≤
      (BitcoinReplacement.chainEnd t₀ Rs).fee * rate.size := by sorry
