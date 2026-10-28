-- Prove2me | Theorems.Thm_BitcoinSubsidy_subsidy_le_maxMoney
-- name    : BitcoinSubsidy.subsidy_le_maxMoney
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:33:20.900799+00:00
-- url     : https://prove2.me/theorems/16d468b6-93c5-4598-8c50-2fdc36cd6087
-- title:
--   The block subsidy is always a valid amount
-- statement:
--   For every block height $h \in \mathbb N$,
--   $$\mathrm{coreSubsidy}(h) \le \mathrm{MAX\_MONEY} = 2.1 \times 10^{15}.$$
--   Since amounts are natural numbers here, this is exactly the `MoneyRange` condition of `consensus/amount.h` applied to the subsidy: it is nonnegative and at most `MAX_MONEY`. The bound is far from tight, as the subsidy never exceeds $5 \times 10^{9}$ satoshi; the point is that the subsidy term of the block reward is always a representable, in-range amount.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, GetBlockSubsidy, src/validation.cpp lines 1833-1844: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L1833; COIN and MAX_MONEY, src/consensus/amount.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/amount.h; nSubsidyHalvingInterval = 210000, CMainParams, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSubsidy

theorem BitcoinSubsidy.subsidy_le_maxMoney (height : Nat) : coreSubsidy height ≤ MAX_MONEY := by sorry
