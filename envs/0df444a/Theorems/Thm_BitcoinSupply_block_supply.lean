-- Prove2me | Theorems.Thm_BitcoinSupply_block_supply
-- name    : BitcoinSupply.block_supply
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T23:51:44.229956+00:00
-- url     : https://prove2.me/theorems/989d3993-b72a-4872-9e48-d021184610b6
-- title:
--   An accepted block raises the UTXO total by at most its subsidy
-- statement:
--   For a reachable state $S$ and `validate S b now = accept S' undo`: `totalValue S'.utxo ≤ totalValue S.utxo + GetBlockSubsidy (S.nextHeight)`. The fees the coinbase collects were already in the ledger; only the subsidy is new value. Proved through the acceptance theorem and `ApplySpec`: the loop bound `totalValue (applyTxs) + totalFees ≤ totalValue + valueOut coinbase` and the coinbase bound `valueOut coinbase ≤ totalFees + subsidy`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockSubsidy, ConnectBlock (the coinbase bound), UpdateCoins, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTxInputs (consensus/tx_verify.cpp); CheckTransaction (consensus/tx_check.cpp); AddCoin, SpendCoin (coins.cpp); MAX_MONEY (consensus/amount.h)

import Definitions.Def_BitcoinSupply
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSubsidy
open BitcoinSupply BitcoinBlockV2

theorem BitcoinSupply.block_supply (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState)
    (undo : BlockUndo) (hR : BitcoinBlockV2.Reachable S) (hv : BitcoinBlockV2.validate S b now = .accept S' undo) :
    BitcoinSupply.totalValue S'.utxo ≤
      BitcoinSupply.totalValue S.utxo + (BitcoinSubsidy.coreSubsidy S.nextHeight : Int) := by sorry
