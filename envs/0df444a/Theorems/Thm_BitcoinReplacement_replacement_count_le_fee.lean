-- Prove2me | Theorems.Thm_BitcoinReplacement_replacement_count_le_fee
-- name    : BitcoinReplacement.replacement_count_le_fee
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:09:23.763993+00:00
-- url     : https://prove2.me/theorems/d275c484-7b53-48d8-a7b4-1d8bbe9c7140
-- title:
--   Each replacement costs at least one satoshi
-- statement:
--   For a rate with positive numerator and a chain of $n$ replacements: $t_0.\text{fee} + n \le t_n.\text{fee}$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.replacement_count_le_fee (rate : BitcoinReplacement.FeeRate)
    (hr : 0 < rate.fee) (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee + Rs.length ≤ (BitcoinReplacement.chainEnd t₀ Rs).fee := by sorry
