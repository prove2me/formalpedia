-- Prove2me | Theorems.Thm_BitcoinUtxo_ledger_bound
-- name    : BitcoinUtxo.ledger_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:24:34.381646+00:00
-- url     : https://prove2.me/theorems/b613b035-1dc6-4dc4-8728-2c71f3b84cef
-- title:
--   From an empty ledger, total value never exceeds the subsidies issued
-- statement:
--   For every subsidy function $s : \mathbb N \to \mathbb Z$, starting height $h$, and sequence of blocks $B_1, \dots, B_n$ whose transactions have pairwise distinct txids within each block, if connecting them from the empty UTXO set succeeds,
--   $$\mathrm{connectChain}_s([\,], h, [B_1, \dots, B_n]) = \mathrm{some}(U) \;\Longrightarrow\; \mathrm{totalValue}(U) \le \sum_{i<n} s(h + i).$$
--   Here `connectChain` applies the transcribed `ConnectBlock` accounting — `CheckTransaction`, the BIP30 check, `CheckTxInputs`, fee accumulation, `UpdateCoins`, and the coinbase bound — at consecutive heights.
--
--   This is the supply bound of the ledger: fees move value between outputs, unspendable outputs destroy it, and the only creation is the coinbase, bounded by fees plus subsidy. With $s$ the mainnet `GetBlockSubsidy` and $h = 1$ (the genesis coinbase is never connected), the right-hand side is below $\mathrm{MAX\_MONEY}$ by the subsidy mission's bound.
--
--   **Formalization Note.** The subsidy is a parameter, so the statement does not depend on the schedule. Distinct txids within a block stand for collision-freedom of transaction hashes, which an abstract id type cannot supply; the BIP30 check is modeled as enforced.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CheckTransaction, src/consensus/tx_check.cpp lines 11-68: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_check.cpp; Consensus::CheckTxInputs, src/consensus/tx_verify.cpp (lines 157-220): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp; CCoinsViewCache::AddCoin, AddCoins, SpendCoin, HaveInputs, src/coins.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp; UpdateCoins, BIP30 check (lines 2396-2475), fee accumulation and coinbase bound in Chainstate::ConnectBlock (lines 2518-2612), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; COIN, MAX_MONEY, MoneyRange, src/consensus/amount.h; COINBASE_MATURITY, src/consensus/consensus.h

import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.ledger_bound {T : Type} [DecidableEq T] (subsidy : Nat → Int) (blocks : List (List (Tx T))) (h : Nat)
    (u' : UtxoSet T) (hnd : ∀ b ∈ blocks, (b.map Tx.txid).Nodup)
    (hc : connectChain subsidy [] h blocks = some u') :
    totalValue u' ≤ subsidySum subsidy h blocks.length := by sorry
