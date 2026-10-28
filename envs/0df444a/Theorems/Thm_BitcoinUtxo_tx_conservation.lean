-- Prove2me | Theorems.Thm_BitcoinUtxo_tx_conservation
-- name    : BitcoinUtxo.tx_conservation
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:23:53.455912+00:00
-- url     : https://prove2.me/theorems/9511ad28-cedf-4f7b-b79f-023bcf9d1e15
-- title:
--   An accepted ordinary transaction cannot create value
-- statement:
--   For every view $U$ with distinct outpoints, non-coinbase transaction $tx$ with distinct inputs, spend height $h$ and fee $f$ such that $\mathrm{checkTxInputs}(U, tx, h) = \mathrm{some}(f)$, provided no outpoint $(tx.\mathrm{txid}, j)$ with $j < |tx.\mathrm{vout}|$ is present in $U$ and every output value is non-negative,
--   $$\mathrm{totalValue}(\mathrm{updateCoins}(U, tx, h)) \le \mathrm{totalValue}(U) - f.$$
--   The ledger loses the fee, and loses more when an output is unspendable. The freshness hypothesis is the BIP30 condition; non-negativity of the outputs comes from `CheckTransaction`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CheckTransaction, src/consensus/tx_check.cpp lines 11-68: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_check.cpp; Consensus::CheckTxInputs, src/consensus/tx_verify.cpp (lines 157-220): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp; CCoinsViewCache::AddCoin, AddCoins, SpendCoin, HaveInputs, src/coins.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp; UpdateCoins, BIP30 check (lines 2396-2475), fee accumulation and coinbase bound in Chainstate::ConnectBlock (lines 2518-2612), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; COIN, MAX_MONEY, MoneyRange, src/consensus/amount.h; COINBASE_MATURITY, src/consensus/consensus.h

import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.tx_conservation {T : Type} [DecidableEq T] (u : UtxoSet T) (tx : Tx T) (h : Nat) (fee : Int)
    (hn : keysNodup u) (hnd : tx.vin.Nodup) (hcb : tx.isCoinbase = false)
    (hfee : checkTxInputs u tx h = some fee)
    (hfresh : ∀ j, j < tx.vout.length → getCoin u ⟨tx.txid, j⟩ = none)
    (hpos : ∀ o ∈ tx.vout, 0 ≤ o.value) :
    totalValue (updateCoins u tx h) ≤ totalValue u - fee := by sorry
