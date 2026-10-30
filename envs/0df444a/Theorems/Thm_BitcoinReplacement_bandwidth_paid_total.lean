-- Prove2me | Theorems.Thm_BitcoinReplacement_bandwidth_paid_total
-- name    : BitcoinReplacement.bandwidth_paid_total
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:06:51.46698+00:00
-- url     : https://prove2.me/theorems/f1774841-663c-4058-959e-963ee7d627c4
-- title:
--   No free relay, total-size form
-- statement:
--   Under the same hypotheses: $t_0.\text{fee} + \text{getFee}\left(\sum_i \text{vsize } t_i\right) \le t_n.\text{fee}$ (the ceiling is subadditive).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.bandwidth_paid_total (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee + rate.getFee (BitcoinReplacement.chainVsizes Rs).sum ≤
      (BitcoinReplacement.chainEnd t₀ Rs).fee := by sorry
