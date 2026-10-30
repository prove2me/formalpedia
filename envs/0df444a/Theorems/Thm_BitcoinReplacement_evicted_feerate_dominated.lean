-- Prove2me | Theorems.Thm_BitcoinReplacement_evicted_feerate_dominated
-- name    : BitcoinReplacement.evicted_feerate_dominated
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:12:05.963046+00:00
-- url     : https://prove2.me/theorems/69f89b44-3aa8-4fd0-8b46-1a1c8f1f922f
-- title:
--   Every direct conflict has a strictly lower fee rate than the replacement
-- statement:
--   For a valid replacement $R$ and $t \in$ `R.direct`: $t.\text{fee} \cdot \text{vsize}(R.\text{new}) < R.\text{new}.\text{fee} \cdot \text{vsize}(t)$. Rule 3, in cross-multiplied form.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.evicted_feerate_dominated (rate : BitcoinReplacement.FeeRate)
    (R : BitcoinReplacement.Replacement) (hR : BitcoinReplacement.Valid rate R)
    (t : BitcoinReplacement.Tx) (ht : t ∈ R.direct) :
    t.fee * R.new.vsize < R.new.fee * t.vsize := by sorry
