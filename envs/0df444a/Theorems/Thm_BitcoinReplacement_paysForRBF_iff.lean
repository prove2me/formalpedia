-- Prove2me | Theorems.Thm_BitcoinReplacement_paysForRBF_iff
-- name    : BitcoinReplacement.paysForRBF_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:05:11.538524+00:00
-- url     : https://prove2.me/theorems/a12654c9-b537-4451-90f6-bff0ef9bc270
-- title:
--   PaysForRBF is one inequality
-- statement:
--   For any rate and replacement: `PaysForRBF rate R` iff `totalFee R.evicted + rate.getFee R.new.vsize ≤ R.new.fee`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.paysForRBF_iff (rate : BitcoinReplacement.FeeRate)
    (R : BitcoinReplacement.Replacement) :
    BitcoinReplacement.PaysForRBF rate R ↔
      BitcoinReplacement.totalFee R.evicted + rate.getFee R.new.vsize ≤ R.new.fee := by sorry
