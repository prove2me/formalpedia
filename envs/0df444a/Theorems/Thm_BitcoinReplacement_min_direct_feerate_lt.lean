-- Prove2me | Theorems.Thm_BitcoinReplacement_min_direct_feerate_lt
-- name    : BitcoinReplacement.min_direct_feerate_lt
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:12:36.99088+00:00
-- url     : https://prove2.me/theorems/d0dd2b6d-df91-4adb-94dc-3bea52c39909
-- title:
--   The lowest-feerate direct conflict is below the replacement
-- statement:
--   For a valid replacement with at least one direct conflict there is a direct conflict $t$ whose exact fee rate is $\le$ every other direct conflict's and $<$ the replacement's.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.min_direct_feerate_lt (rate : BitcoinReplacement.FeeRate)
    (R : BitcoinReplacement.Replacement) (hR : BitcoinReplacement.Valid rate R)
    (hne : R.direct ≠ 0) :
    ∃ t ∈ R.direct, (∀ s ∈ R.direct, t.feeRateQ ≤ s.feeRateQ) ∧
      t.feeRateQ < R.new.feeRateQ := by sorry
