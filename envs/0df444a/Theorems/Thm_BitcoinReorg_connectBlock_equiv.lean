-- Prove2me | Theorems.Thm_BitcoinReorg_connectBlock_equiv
-- name    : BitcoinReorg.connectBlock_equiv
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T01:24:42.656607+00:00
-- url     : https://prove2.me/theorems/3b1fcf7c-a198-42b7-9d4d-62f2ce78cab8
-- title:
--   ConnectBlock respects ledger equivalence
-- statement:
--   For two states with the same headers and equivalent ledgers, `connectBlock` on the same block either fails on both or succeeds on both with equivalent ledgers and the same undo data. Every ledger read of the transaction loop — `CheckTxInputs`, `SequenceLocks`, the sigop cost, `CheckInputScripts`, the undo record, the BIP30 scan — goes through `getCoin`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock, DisconnectBlock, UpdateCoins, ApplyTxInUndo, Chainstate::ConnectTip, Chainstate::DisconnectTip, Chainstate::ActivateBestChainStep, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CCoinsViewCache (coins.cpp)

import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

theorem BitcoinReorg.connectBlock_equiv (H : List BitcoinSer.Header) (u v : Ledger) (h : BitcoinBlockV2.Equiv u v)
    (b : BitcoinSer.Block) :
    (BitcoinBlockV2.connectBlock ⟨H, u⟩ b = none ∧ BitcoinBlockV2.connectBlock ⟨H, v⟩ b = none) ∨
    (∃ u' v' undo, BitcoinBlockV2.connectBlock ⟨H, u⟩ b = some (u', undo) ∧
      BitcoinBlockV2.connectBlock ⟨H, v⟩ b = some (v', undo) ∧ BitcoinBlockV2.Equiv u' v') := by sorry
