-- Prove2me | Theorems.Thm_BitcoinReorg_connectChain_equiv
-- name    : BitcoinReorg.connectChain_equiv
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T01:25:45.160983+00:00
-- url     : https://prove2.me/theorems/b8c43dbc-d3e7-4f52-ada3-77e3806f7425
-- title:
--   connectChain respects state equivalence
-- statement:
--   Connecting the same chain to two `StateEquiv` states either fails on both or succeeds on both with `StateEquiv` results and the same undo data.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock, DisconnectBlock, UpdateCoins, ApplyTxInUndo, Chainstate::ConnectTip, Chainstate::DisconnectTip, Chainstate::ActivateBestChainStep, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CCoinsViewCache (coins.cpp)

import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

theorem BitcoinReorg.connectChain_equiv (bs : List (BitcoinSer.Block × Int)) :
    ∀ (S T : ChainState), BitcoinReorg.StateEquiv S T →
    (BitcoinReorg.connectChain S bs = none ∧ BitcoinReorg.connectChain T bs = none) ∨
    (∃ U V undos, BitcoinReorg.connectChain S bs = some (U, undos) ∧ BitcoinReorg.connectChain T bs = some (V, undos) ∧
      BitcoinReorg.StateEquiv U V) := by sorry
