-- Prove2me | Theorems.Thm_BitcoinReplacement_feeRateQ_lt_iff
-- name    : BitcoinReplacement.feeRateQ_lt_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:11:41.445466+00:00
-- url     : https://prove2.me/theorems/97711924-f3ea-453c-aa3e-3e37c093610c
-- title:
--   The ByRatio comparison is the comparison of exact fractions
-- statement:
--   For transactions $a, b$: $a.\text{fee}/a.\text{vsize} < b.\text{fee}/b.\text{vsize}$ in $\mathbb{Q}$ iff `FeeRate.lt a.feeRate b.feeRate`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.feeRateQ_lt_iff (a b : BitcoinReplacement.Tx) :
    a.feeRateQ < b.feeRateQ ↔ BitcoinReplacement.FeeRate.lt a.feeRate b.feeRate := by sorry
