-- Prove2me | Theorems.Thm_BitcoinUtxo_totalValue_spend
-- name    : BitcoinUtxo.totalValue_spend
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:23:21.151912+00:00
-- url     : https://prove2.me/theorems/c5ff9b89-fdd2-4bb2-8d4e-04b49a168fa8
-- title:
--   Spending a present coin removes exactly its value
-- statement:
--   For every view $U$ with pairwise distinct outpoints, outpoint $p$ and coin $c$ with $\mathrm{getCoin}(U, p) = \mathrm{some}(c)$,
--   $$\mathrm{totalValue}(\mathrm{spendCoin}(U, p)) = \mathrm{totalValue}(U) - c.\mathrm{value}.$$
--   Distinctness is what makes the removed entry unique.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CheckTransaction, src/consensus/tx_check.cpp lines 11-68: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_check.cpp; Consensus::CheckTxInputs, src/consensus/tx_verify.cpp (lines 157-220): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp; CCoinsViewCache::AddCoin, AddCoins, SpendCoin, HaveInputs, src/coins.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp; UpdateCoins, BIP30 check (lines 2396-2475), fee accumulation and coinbase bound in Chainstate::ConnectBlock (lines 2518-2612), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; COIN, MAX_MONEY, MoneyRange, src/consensus/amount.h; COINBASE_MATURITY, src/consensus/consensus.h

import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.totalValue_spend {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (c : Coin)
    (hn : keysNodup u) (h : getCoin u op = some c) :
    totalValue (spendCoin u op) = totalValue u - c.out.value := by sorry
