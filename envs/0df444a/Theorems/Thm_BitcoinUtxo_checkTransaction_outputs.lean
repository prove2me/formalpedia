-- Prove2me | Theorems.Thm_BitcoinUtxo_checkTransaction_outputs
-- name    : BitcoinUtxo.checkTransaction_outputs
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:23:03.294732+00:00
-- url     : https://prove2.me/theorems/4b73b57c-9a56-42db-93f7-d5dc9b1ae833
-- title:
--   CheckTransaction yields distinct inputs and in-range outputs
-- statement:
--   For every transaction $tx$ with $\mathrm{checkTransaction}(tx) = \mathtt{true}$: the input outpoints of $tx$ are pairwise distinct, and every output value $v$ of $tx$ satisfies $0 \le v \le \mathrm{MAX\_MONEY}$. These are the two facts of `CheckTransaction` that the value accounting consumes: the duplicate-input rejection (CVE-2018-17144) and the output-range loop (CVE-2010-5139).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CheckTransaction, src/consensus/tx_check.cpp lines 11-68: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_check.cpp; Consensus::CheckTxInputs, src/consensus/tx_verify.cpp (lines 157-220): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp; CCoinsViewCache::AddCoin, AddCoins, SpendCoin, HaveInputs, src/coins.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp; UpdateCoins, BIP30 check (lines 2396-2475), fee accumulation and coinbase bound in Chainstate::ConnectBlock (lines 2518-2612), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; COIN, MAX_MONEY, MoneyRange, src/consensus/amount.h; COINBASE_MATURITY, src/consensus/consensus.h

import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.checkTransaction_outputs {T : Type} [DecidableEq T] (tx : Tx T) (h : checkTransaction tx = true) :
    tx.vin.Nodup ∧ ∀ o ∈ tx.vout, 0 ≤ o.value ∧ o.value ≤ MAX_MONEY := by sorry
