-- Prove2me | Theorems.Thm_BitcoinSupply_supply_bound
-- name    : BitcoinSupply.supply_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T23:52:24.430392+00:00
-- url     : https://prove2.me/theorems/4eb0c65f-70dc-462d-a4b8-281369e59adb
-- title:
--   The supply invariant: the UTXO total never exceeds the issued subsidy
-- statement:
--   For every chain state $S$ reachable from the genesis: `totalValue S.utxo + genesisSubsidy ≤ issued S.nextHeight`. The spendable supply plus the unspendable genesis subsidy is bounded by what `GetBlockSubsidy` has issued to the chain's height. No sequence of valid blocks creates value beyond the schedule: this is the invariant whose violation would be an inflation bug (CVE-2018-17144 broke it in Core by double-spending within a block; here duplicate inputs are rejected by `CheckTransaction` and the proof goes through the distinct-prevout condition).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockSubsidy, ConnectBlock (the coinbase bound), UpdateCoins, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTxInputs (consensus/tx_verify.cpp); CheckTransaction (consensus/tx_check.cpp); AddCoin, SpendCoin (coins.cpp); MAX_MONEY (consensus/amount.h)

import Definitions.Def_BitcoinSupply
open BitcoinSupply BitcoinBlockV2

theorem BitcoinSupply.supply_bound (S : ChainState) (hR : BitcoinBlockV2.Reachable S) :
    BitcoinSupply.totalValue S.utxo + BitcoinSupply.genesisSubsidy ≤ BitcoinSupply.issued S.nextHeight := by sorry
