-- Prove2me | Theorems.Thm_BitcoinUtxo_chain_bound
-- name    : BitcoinUtxo.chain_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:24:26.007986+00:00
-- url     : https://prove2.me/theorems/7caa26b2-6fff-418f-8ca4-55da22ff9b8d
-- title:
--   A chain of accepted blocks raises the ledger by at most the summed subsidies
-- statement:
--   For every subsidy function $s$, list of blocks $B_1, \dots, B_n$ each with pairwise distinct txids, view $U$ with distinct outpoints and height $h$, if $\mathrm{connectChain}_s(U, h, [B_1, \dots, B_n]) = \mathrm{some}(U')$ then
--   $$\mathrm{totalValue}(U') \le \mathrm{totalValue}(U) + \sum_{i<n} s(h + i).$$
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CheckTransaction, src/consensus/tx_check.cpp lines 11-68: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_check.cpp; Consensus::CheckTxInputs, src/consensus/tx_verify.cpp (lines 157-220): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp; CCoinsViewCache::AddCoin, AddCoins, SpendCoin, HaveInputs, src/coins.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp; UpdateCoins, BIP30 check (lines 2396-2475), fee accumulation and coinbase bound in Chainstate::ConnectBlock (lines 2518-2612), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; COIN, MAX_MONEY, MoneyRange, src/consensus/amount.h; COINBASE_MATURITY, src/consensus/consensus.h

import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.chain_bound {T : Type} [DecidableEq T] (subsidy : Nat → Int) :
    ∀ (blocks : List (List (Tx T))) (u : UtxoSet T) (h : Nat) (u' : UtxoSet T),
      keysNodup u → (∀ b ∈ blocks, (b.map Tx.txid).Nodup) →
      connectChain subsidy u h blocks = some u' →
      totalValue u' ≤ totalValue u + subsidySum subsidy h blocks.length := by sorry
