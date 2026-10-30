-- Prove2me | Theorems.Thm_BitcoinReplacement_bandwidth_paid_real
-- name    : BitcoinReplacement.bandwidth_paid_real
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:07:54.704985+00:00
-- url     : https://prove2.me/theorems/280fdfbb-aa26-45a2-abd6-37f04524b84b
-- title:
--   No free relay, rational form
-- statement:
--   Under the same hypotheses, in $\mathbb{Q}$: $t_0.\text{fee} + \frac{\text{fee}}{\text{size}} \sum_i \text{vsize } t_i \le t_n.\text{fee}$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.bandwidth_paid_real (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    (t₀.fee : ℚ) + ((rate.fee : ℚ) / rate.size) * (BitcoinReplacement.chainVsizes Rs).sum ≤
      ((BitcoinReplacement.chainEnd t₀ Rs).fee : ℚ) := by sorry
