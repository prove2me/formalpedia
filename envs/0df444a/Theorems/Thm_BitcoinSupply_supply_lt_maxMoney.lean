-- Prove2me | Theorems.Thm_BitcoinSupply_supply_lt_maxMoney
-- name    : BitcoinSupply.supply_lt_maxMoney
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T23:53:19.093062+00:00
-- url     : https://prove2.me/theorems/a53c8778-76b5-4483-8eb2-86aff66341a7
-- title:
--   The spendable supply is always below MAX_MONEY
-- statement:
--   For every reachable chain state $S$: `totalValue S.utxo < MAX_MONEY` (= 21,000,000 × 10^8 satoshi). From the supply invariant and the subsidy mission's `issuance_bound`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockSubsidy, ConnectBlock (the coinbase bound), UpdateCoins, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTxInputs (consensus/tx_verify.cpp); CheckTransaction (consensus/tx_check.cpp); AddCoin, SpendCoin (coins.cpp); MAX_MONEY (consensus/amount.h)

import Definitions.Def_BitcoinSupply
open BitcoinSupply BitcoinBlockV2

theorem BitcoinSupply.supply_lt_maxMoney (S : ChainState) (hR : BitcoinBlockV2.Reachable S) :
    BitcoinSupply.totalValue S.utxo < MAX_MONEY := by sorry
