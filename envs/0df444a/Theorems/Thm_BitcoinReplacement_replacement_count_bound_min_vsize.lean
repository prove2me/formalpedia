-- Prove2me | Theorems.Thm_BitcoinReplacement_replacement_count_bound_min_vsize
-- name    : BitcoinReplacement.replacement_count_bound_min_vsize
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T14:08:30.610094+00:00
-- url     : https://prove2.me/theorems/a6a4cb85-8a89-4ce1-970c-5d20783afd88
-- title:
--   The number of replacements is bounded by the fee gained, per minimum size
-- statement:
--   For a chain of $n$ replacements each of virtual size at least $m$: $t_0.\text{fee} + n \cdot \text{getFee}(m) \le t_n.\text{fee}$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.replacement_count_bound_min_vsize (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) (m : ℕ) (hm : ∀ R ∈ Rs, m ≤ R.new.vsize) :
    t₀.fee + Rs.length * rate.getFee m ≤ (BitcoinReplacement.chainEnd t₀ Rs).fee := by sorry
