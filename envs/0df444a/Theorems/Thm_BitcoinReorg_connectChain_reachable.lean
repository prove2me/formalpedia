-- Prove2me | Theorems.Thm_BitcoinReorg_connectChain_reachable
-- name    : BitcoinReorg.connectChain_reachable
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T01:25:27.312307+00:00
-- url     : https://prove2.me/theorems/572c6cb3-7615-4519-968e-e5a2855e4fd8
-- title:
--   Every state along a connected chain is reachable
-- statement:
--   If `S` is reachable and `connectChain S bs = some (T, undos)`, then `T` is reachable: `connectChain` is iterated `validate`, and `Reachable` is closed under accepted blocks.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock, DisconnectBlock, UpdateCoins, ApplyTxInUndo, Chainstate::ConnectTip, Chainstate::DisconnectTip, Chainstate::ActivateBestChainStep, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CCoinsViewCache (coins.cpp)

import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

theorem BitcoinReorg.connectChain_reachable (S : ChainState) (hR : BitcoinBlockV2.Reachable S) :
    ∀ (bs : List (BitcoinSer.Block × Int)) (T : ChainState) (undos : List BlockUndo),
    BitcoinReorg.connectChain S bs = some (T, undos) → BitcoinBlockV2.Reachable T := by sorry
