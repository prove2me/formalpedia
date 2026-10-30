-- Prove2me | Theorems.Thm_BitcoinReplacement_pinning_cost
-- name    : BitcoinReplacement.pinning_cost
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:10:40.102476+00:00
-- url     : https://prove2.me/theorems/789bd871-d7eb-4add-bb7c-e8fa9ed0336e
-- title:
--   Pinning: descendants attached to a transaction raise the cost of replacing it by their total fee
-- statement:
--   For a valid replacement $R$, a transaction $t$ and a multiset $D$ with $t ::ₘ D \le$ `R.evicted`: $t.\text{fee} + \text{totalFee}(D) + \text{getFee}(\text{vsize } R.\text{new}) \le R.\text{new}.\text{fee}$. Whoever attaches descendants of total fee $F$ to $t$ forces any replacement of $t$ to pay at least $F$ more.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.pinning_cost (rate : BitcoinReplacement.FeeRate)
    (t : BitcoinReplacement.Tx) (D : Multiset BitcoinReplacement.Tx)
    (R : BitcoinReplacement.Replacement) (hR : BitcoinReplacement.Valid rate R)
    (hD : t ::ₘ D ≤ R.evicted) :
    t.fee + BitcoinReplacement.totalFee D + rate.getFee R.new.vsize ≤ R.new.fee := by sorry
