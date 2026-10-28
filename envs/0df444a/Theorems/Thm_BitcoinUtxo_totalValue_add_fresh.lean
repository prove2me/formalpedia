-- Prove2me | Theorems.Thm_BitcoinUtxo_totalValue_add_fresh
-- name    : BitcoinUtxo.totalValue_add_fresh
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:23:31.729409+00:00
-- url     : https://prove2.me/theorems/2c9d6758-6885-4754-b853-71d3b7a44788
-- title:
--   Adding a coin at a fresh outpoint adds its value, or nothing if unspendable
-- statement:
--   For every view $U$, outpoint $p$ absent from $U$, and coin $c$,
--   $$\mathrm{totalValue}(\mathrm{addCoin}(U, p, c)) = \mathrm{totalValue}(U) + \begin{cases} 0 & c \text{ unspendable} \\ c.\mathrm{value} & \text{otherwise.}\end{cases}$$
--   This is `AddCoin` on a fresh outpoint: an `OP_RETURN`-style output is dropped, any other is stored.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CheckTransaction, src/consensus/tx_check.cpp lines 11-68: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_check.cpp; Consensus::CheckTxInputs, src/consensus/tx_verify.cpp (lines 157-220): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp; CCoinsViewCache::AddCoin, AddCoins, SpendCoin, HaveInputs, src/coins.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp; UpdateCoins, BIP30 check (lines 2396-2475), fee accumulation and coinbase bound in Chainstate::ConnectBlock (lines 2518-2612), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; COIN, MAX_MONEY, MoneyRange, src/consensus/amount.h; COINBASE_MATURITY, src/consensus/consensus.h

import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.totalValue_add_fresh {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (c : Coin)
    (h : getCoin u op = none) :
    totalValue (addCoin u op c) = totalValue u + (if c.out.unspendable then 0 else c.out.value) := by sorry
