-- Prove2me | Theorems.Thm_BitcoinSubsidy_issuance_le_total
-- name    : BitcoinSubsidy.issuance_le_total
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:34:06.168145+00:00
-- url     : https://prove2.me/theorems/99a8fd89-800c-440b-9d84-eeca20dd4f37
-- title:
--   Cumulative issuance is bounded by the final total
-- statement:
--   For every $n \in \mathbb N$,
--   $$\mathrm{issuedBelow}(n) \le 2{,}099{,}999{,}997{,}690{,}000 .$$
--   The cumulative subsidy below any height is at most the total reached at the zero height: below it the sum is still growing, and from it on every further term is zero, so the sum is constant. This is the exact form of the supply bound for the subsidy schedule alone.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, GetBlockSubsidy, src/validation.cpp lines 1833-1844: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L1833; COIN and MAX_MONEY, src/consensus/amount.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/amount.h; nSubsidyHalvingInterval = 210000, CMainParams, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSubsidy

theorem BitcoinSubsidy.issuance_le_total (n : Nat) : issuedBelow n ≤ 2099999997690000 := by sorry
