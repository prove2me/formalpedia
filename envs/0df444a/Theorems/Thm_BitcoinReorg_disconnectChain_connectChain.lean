-- Prove2me | Theorems.Thm_BitcoinReorg_disconnectChain_connectChain
-- name    : BitcoinReorg.disconnectChain_connectChain
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T01:25:59.160351+00:00
-- url     : https://prove2.me/theorems/9f86e3d4-95c6-440f-abdc-9aa9f0e777e6
-- title:
--   Multi-block undo: a connected chain is disconnected back to its starting state
-- statement:
--   For a reachable `S`, a chain `bs` satisfying `FreshChain S bs`, and `connectChain S bs = some (T, undos)`: disconnecting from `T` the blocks of `bs` with their undo data, tip first, succeeds with every disconnect clean and yields a state `StateEquiv` to `S`. The undo data recorded over any number of blocks restores the chain state exactly, up to ledger order.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock, DisconnectBlock, UpdateCoins, ApplyTxInUndo, Chainstate::ConnectTip, Chainstate::DisconnectTip, Chainstate::ActivateBestChainStep, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CCoinsViewCache (coins.cpp)

import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

theorem BitcoinReorg.disconnectChain_connectChain (bs : List (BitcoinSer.Block × Int)) :
    ∀ (S : ChainState), BitcoinBlockV2.Reachable S → BitcoinReorg.FreshChain S bs →
    ∀ (T : ChainState) (undos : List BlockUndo), BitcoinReorg.connectChain S bs = some (T, undos) →
    ∃ S', BitcoinReorg.disconnectChain T ((bs.map Prod.fst).zip undos).reverse = some (S', true) ∧
      BitcoinReorg.StateEquiv S' S := by sorry
