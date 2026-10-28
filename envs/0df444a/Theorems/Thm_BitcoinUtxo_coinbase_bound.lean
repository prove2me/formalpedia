-- Prove2me | Theorems.Thm_BitcoinUtxo_coinbase_bound
-- name    : BitcoinUtxo.coinbase_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:24:07.882295+00:00
-- url     : https://prove2.me/theorems/1f9dc0ba-268a-4b6a-88ae-1dbcc62a146d
-- title:
--   A coinbase adds at most its output value
-- statement:
--   For every view $U$, coinbase transaction $tx$, height $h$, provided no outpoint $(tx.\mathrm{txid}, j)$ with $j < |tx.\mathrm{vout}|$ is present in $U$ and every output value is non-negative,
--   $$\mathrm{totalValue}(\mathrm{updateCoins}(U, tx, h)) \le \mathrm{totalValue}(U) + \mathrm{valueOut}(tx).$$
--   Equality holds when no output is unspendable.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CheckTransaction, src/consensus/tx_check.cpp lines 11-68: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_check.cpp; Consensus::CheckTxInputs, src/consensus/tx_verify.cpp (lines 157-220): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp; CCoinsViewCache::AddCoin, AddCoins, SpendCoin, HaveInputs, src/coins.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp; UpdateCoins, BIP30 check (lines 2396-2475), fee accumulation and coinbase bound in Chainstate::ConnectBlock (lines 2518-2612), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; COIN, MAX_MONEY, MoneyRange, src/consensus/amount.h; COINBASE_MATURITY, src/consensus/consensus.h

import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.coinbase_bound {T : Type} [DecidableEq T] (u : UtxoSet T) (tx : Tx T) (h : Nat)
    (hcb : tx.isCoinbase = true)
    (hfresh : ∀ j, j < tx.vout.length → getCoin u ⟨tx.txid, j⟩ = none)
    (hpos : ∀ o ∈ tx.vout, 0 ≤ o.value) :
    totalValue (updateCoins u tx h) ≤ totalValue u + valueOut tx := by sorry
