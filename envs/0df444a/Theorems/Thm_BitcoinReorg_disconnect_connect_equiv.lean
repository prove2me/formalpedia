-- Prove2me | Theorems.Thm_BitcoinReorg_disconnect_connect_equiv
-- name    : BitcoinReorg.disconnect_connect_equiv
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T01:25:10.945351+00:00
-- url     : https://prove2.me/theorems/cf390c30-fd5f-474d-99a0-88a38fbb7f71
-- title:
--   Disconnect undoes connect, from any equivalent ledger
-- statement:
--   The block mission's `disconnect_connect` for any ledger with the same coins as the accepted state's: under its hypotheses (well-formed state, distinct and fresh txids, not the genesis hash), `disconnectBlock` on that ledger with the recorded undo data succeeds cleanly and yields a ledger equivalent to the state before the block.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock, DisconnectBlock, UpdateCoins, ApplyTxInUndo, Chainstate::ConnectTip, Chainstate::DisconnectTip, Chainstate::ActivateBestChainStep, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CCoinsViewCache (coins.cpp)

import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

theorem BitcoinReorg.disconnect_connect_equiv (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState)
    (undo : BlockUndo) (hwf : BitcoinBlockV2.WellFormed S) (hnd : (b.vtx.map BitcoinSer.txid).Nodup)
    (hfresh : ∀ tx ∈ b.vtx, ∀ o, BitcoinBlockV2.getCoin S.utxo ⟨BitcoinSer.txid tx, o⟩ = none)
    (hg : BitcoinSer.headerHash b.header ≠ BitcoinSer.genesisHash)
    (h : BitcoinBlockV2.validate S b now = .accept S' undo) (v : Ledger) (hv : BitcoinBlockV2.Equiv v S'.utxo) :
    ∃ u, BitcoinBlockV2.disconnectBlock v S.nextHeight (BitcoinSer.headerHash b.header) b undo = some (u, true) ∧
      BitcoinBlockV2.Equiv u S.utxo := by sorry
