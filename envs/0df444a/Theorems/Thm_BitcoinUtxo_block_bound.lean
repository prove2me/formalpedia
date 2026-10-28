-- Prove2me | Theorems.Thm_BitcoinUtxo_block_bound
-- name    : BitcoinUtxo.block_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:24:16.877485+00:00
-- url     : https://prove2.me/theorems/f26c9438-68f4-4211-a828-f182e22902bd
-- title:
--   An accepted block raises the ledger by at most the subsidy
-- statement:
--   For every subsidy function $s$, view $U$ with distinct outpoints, height $h$, and block $B$ whose transactions have pairwise distinct txids, if $\mathrm{connectBlock}_s(U, h, B) = \mathrm{some}(U', \mathrm{fees})$ then
--   $$\mathrm{totalValue}(U') \le \mathrm{totalValue}(U) + s(h),$$
--   and $U'$ has pairwise distinct outpoints. The fees paid by the block's transactions leave the ledger and are returned to it by the coinbase, which may add at most $s(h)$ beyond them.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CheckTransaction, src/consensus/tx_check.cpp lines 11-68: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_check.cpp; Consensus::CheckTxInputs, src/consensus/tx_verify.cpp (lines 157-220): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp; CCoinsViewCache::AddCoin, AddCoins, SpendCoin, HaveInputs, src/coins.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp; UpdateCoins, BIP30 check (lines 2396-2475), fee accumulation and coinbase bound in Chainstate::ConnectBlock (lines 2518-2612), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; COIN, MAX_MONEY, MoneyRange, src/consensus/amount.h; COINBASE_MATURITY, src/consensus/consensus.h

import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.block_bound {T : Type} [DecidableEq T] (subsidy : Nat → Int) (u : UtxoSet T) (h : Nat) (block : List (Tx T))
    (u' : UtxoSet T) (fees : Int) (hn : keysNodup u) (hnd : (block.map Tx.txid).Nodup)
    (hc : connectBlock subsidy u h block = some (u', fees)) :
    totalValue u' ≤ totalValue u + subsidy h ∧ keysNodup u' := by sorry
