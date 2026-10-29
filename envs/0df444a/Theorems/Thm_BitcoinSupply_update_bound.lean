-- Prove2me | Theorems.Thm_BitcoinSupply_update_bound
-- name    : BitcoinSupply.update_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T23:49:51.896053+00:00
-- url     : https://prove2.me/theorems/9433a594-30e4-4818-b478-7ccbe272250a
-- title:
--   UpdateCoins creates at most the output value and destroys the input value
-- statement:
--   For a ledger $u$ with distinct keys and non-negative coin values, and a transaction with non-negative outputs, distinct prevouts, and (unless it is a coinbase) every input present in $u$: `totalValue (updateCoins u tx H) ≤ totalValue u + valueOut tx − (if coinbase then 0 else valueIn u tx.vin)`. The inequality (rather than equality) absorbs unspendable outputs, which `AddCoin` does not store, and overwritten coins.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockSubsidy, ConnectBlock (the coinbase bound), UpdateCoins, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTxInputs (consensus/tx_verify.cpp); CheckTransaction (consensus/tx_check.cpp); AddCoin, SpendCoin (coins.cpp); MAX_MONEY (consensus/amount.h)

import Definitions.Def_BitcoinSupply
import Definitions.Def_BitcoinSer
open BitcoinSupply BitcoinBlockV2

theorem BitcoinSupply.update_bound (u : Ledger) (tx : BitcoinSer.Tx) (H : Nat) (hnd : BitcoinBlockV2.keysNodup u)
    (hnn : ∀ e ∈ u, 0 ≤ e.2.out.nValue) (hos : ∀ o ∈ tx.vout, 0 ≤ o.nValue)
    (hdup : (tx.vin.map BitcoinSer.TxIn.prevout).Nodup)
    (hin : BitcoinBlockV2.isCoinBase tx = false → ∀ i ∈ tx.vin, BitcoinBlockV2.haveCoin u i.prevout = true) :
    BitcoinSupply.totalValue (BitcoinBlockV2.updateCoins u tx H) ≤
      BitcoinSupply.totalValue u + BitcoinBlockV2.valueOut tx -
        (if BitcoinBlockV2.isCoinBase tx then 0 else BitcoinBlockV2.valueIn u tx.vin) := by sorry
