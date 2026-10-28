-- Prove2me | Theorems.Thm_BitcoinUtxo_totalValue_spendInputs
-- name    : BitcoinUtxo.totalValue_spendInputs
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:23:45.424765+00:00
-- url     : https://prove2.me/theorems/ad3ac049-f789-4ab4-b08d-76d1cd9531ee
-- title:
--   Spending distinct present inputs removes exactly valueIn
-- statement:
--   For every view $U$ with pairwise distinct outpoints and list of outpoints $I$ that is itself duplicate-free and all of whose members are present in $U$,
--   $$\mathrm{totalValue}(\mathrm{spendInputs}(U, I)) = \mathrm{totalValue}(U) - \mathrm{valueIn}(U, I).$$
--   Without distinctness of $I$ the identity fails: a repeated outpoint is counted twice in `valueIn` but removed once.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CheckTransaction, src/consensus/tx_check.cpp lines 11-68: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_check.cpp; Consensus::CheckTxInputs, src/consensus/tx_verify.cpp (lines 157-220): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp; CCoinsViewCache::AddCoin, AddCoins, SpendCoin, HaveInputs, src/coins.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp; UpdateCoins, BIP30 check (lines 2396-2475), fee accumulation and coinbase bound in Chainstate::ConnectBlock (lines 2518-2612), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; COIN, MAX_MONEY, MoneyRange, src/consensus/amount.h; COINBASE_MATURITY, src/consensus/consensus.h

import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.totalValue_spendInputs {T : Type} [DecidableEq T] (u : UtxoSet T) :
    ∀ (ops : List (OutPoint T)), keysNodup u → ops.Nodup → (∀ op ∈ ops, haveCoin u op = true) →
      totalValue (spendInputs u ops) = totalValue u - valueIn u ops := by sorry
