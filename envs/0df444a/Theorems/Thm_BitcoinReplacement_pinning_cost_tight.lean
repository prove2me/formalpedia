-- Prove2me | Theorems.Thm_BitcoinReplacement_pinning_cost_tight
-- name    : BitcoinReplacement.pinning_cost_tight
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:11:10.791754+00:00
-- url     : https://prove2.me/theorems/582d2c2b-b3b5-4dc9-abcc-00cd88d6d79d
-- title:
--   The pinning bound is exactly rule 4
-- statement:
--   If `R.evicted = t ::ₘ D` then `PaysForRBF rate R` iff $t.\text{fee} + \text{totalFee}(D) + \text{getFee}(\text{vsize } R.\text{new}) \le R.\text{new}.\text{fee}$: the bound of `pinning_cost` is attained, so the pinning cost is neither more nor less than the descendants' fees plus the incremental fee.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.pinning_cost_tight (rate : BitcoinReplacement.FeeRate)
    (t : BitcoinReplacement.Tx) (D : Multiset BitcoinReplacement.Tx)
    (R : BitcoinReplacement.Replacement) (hE : R.evicted = t ::ₘ D) :
    BitcoinReplacement.PaysForRBF rate R ↔
      t.fee + BitcoinReplacement.totalFee D + rate.getFee R.new.vsize ≤ R.new.fee := by sorry
