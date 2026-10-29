-- Prove2me | Theorems.Thm_BitcoinReorg_reorg_safety
-- name    : BitcoinReorg.reorg_safety
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T01:26:25.068968+00:00
-- url     : https://prove2.me/theorems/077a4d36-2687-4449-a9d3-0d8172e11ae5
-- title:
--   Reorganization safety: disconnect then connect yields a reachable state, up to ledger order
-- statement:
--   Let `S` be reachable, `bs` a chain with `FreshChain S bs` connected to `S` giving `T` with undo data `undos`; let the blocks of `bs` be disconnected from `T` with that undo data (tip first) giving `S'` with flag `clean`; and let any chain `cs` be connected to `S'` giving `U` with undo data `undos'`. Then `clean = true`, and connecting `cs` directly to `S` succeeds with the same undo data `undos'` and a state `U₀` such that `StateEquiv U U₀` and `U₀` is reachable from the genesis. The UTXO set a node holds after any reorganization is, up to the order of its ledger, the one it would hold had it validated the new branch directly: the state is a function of the chain, not of the path taken to it.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock, DisconnectBlock, UpdateCoins, ApplyTxInUndo, Chainstate::ConnectTip, Chainstate::DisconnectTip, Chainstate::ActivateBestChainStep, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CCoinsViewCache (coins.cpp)

import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

theorem BitcoinReorg.reorg_safety (S : ChainState) (hR : BitcoinBlockV2.Reachable S)
    (bs : List (BitcoinSer.Block × Int)) (hF : BitcoinReorg.FreshChain S bs)
    (T : ChainState) (undos : List BlockUndo) (hc : BitcoinReorg.connectChain S bs = some (T, undos))
    (S' : ChainState) (clean : Bool)
    (hd : BitcoinReorg.disconnectChain T ((bs.map Prod.fst).zip undos).reverse = some (S', clean))
    (cs : List (BitcoinSer.Block × Int)) (U : ChainState) (undos' : List BlockUndo)
    (hc' : BitcoinReorg.connectChain S' cs = some (U, undos')) :
    clean = true ∧ ∃ U₀, BitcoinReorg.connectChain S cs = some (U₀, undos') ∧ BitcoinReorg.StateEquiv U U₀ ∧
      BitcoinBlockV2.Reachable U₀ := by sorry
