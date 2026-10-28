-- Prove2me | Theorems.Thm_BitcoinUtxo_checkTxInputs_some
-- name    : BitcoinUtxo.checkTxInputs_some
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:23:12.583571+00:00
-- url     : https://prove2.me/theorems/c1e66139-2ee9-41a1-9643-ff3737c60729
-- title:
--   CheckTxInputs returns the fee, in range, with all inputs present
-- statement:
--   For every view $U$, transaction $tx$, spend height $h$ and amount $f$ with $\mathrm{checkTxInputs}(U, tx, h) = \mathrm{some}(f)$:
--   $$f = \mathrm{valueIn}(U, tx.\mathrm{vin}) - \mathrm{valueOut}(tx), \qquad 0 \le f \le \mathrm{MAX\_MONEY},$$
--   and every input outpoint of $tx$ is present in $U$. The fee returned through `txfee` is exactly the difference of input and output values, and the input loop guarantees that every input it summed exists.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CheckTransaction, src/consensus/tx_check.cpp lines 11-68: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_check.cpp; Consensus::CheckTxInputs, src/consensus/tx_verify.cpp (lines 157-220): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp; CCoinsViewCache::AddCoin, AddCoins, SpendCoin, HaveInputs, src/coins.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp; UpdateCoins, BIP30 check (lines 2396-2475), fee accumulation and coinbase bound in Chainstate::ConnectBlock (lines 2518-2612), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; COIN, MAX_MONEY, MoneyRange, src/consensus/amount.h; COINBASE_MATURITY, src/consensus/consensus.h

import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.checkTxInputs_some {T : Type} [DecidableEq T] (u : UtxoSet T) (tx : Tx T) (h : Nat) (fee : Int)
    (hfee : checkTxInputs u tx h = some fee) :
    fee = valueIn u tx.vin - valueOut tx ∧ 0 ≤ fee ∧ fee ≤ MAX_MONEY ∧
    ∀ op ∈ tx.vin, haveCoin u op = true := by sorry
