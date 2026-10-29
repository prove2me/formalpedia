-- Prove2me | Theorems.Thm_BitcoinSupply_values_in_range
-- name    : BitcoinSupply.values_in_range
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T23:51:15.847626+00:00
-- url     : https://prove2.me/theorems/16767439-4b48-47cd-bef6-f89b73ed7af9
-- title:
--   Every coin of a reachable state has a value in [0, MAX_MONEY]
-- statement:
--   For every chain state $S$ reachable from the genesis, `ValuesInRange S.utxo`: coins enter the ledger only as outputs of transactions that passed `CheckTransaction`, whose output loop enforces `MoneyRange` on each value.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockSubsidy, ConnectBlock (the coinbase bound), UpdateCoins, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTxInputs (consensus/tx_verify.cpp); CheckTransaction (consensus/tx_check.cpp); AddCoin, SpendCoin (coins.cpp); MAX_MONEY (consensus/amount.h)

import Definitions.Def_BitcoinSupply
open BitcoinSupply BitcoinBlockV2

theorem BitcoinSupply.values_in_range (S : ChainState) (hR : BitcoinBlockV2.Reachable S) :
    BitcoinSupply.ValuesInRange S.utxo := by sorry
