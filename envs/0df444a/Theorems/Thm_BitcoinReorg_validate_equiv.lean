-- Prove2me | Theorems.Thm_BitcoinReorg_validate_equiv
-- name    : BitcoinReorg.validate_equiv
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T01:24:54.231795+00:00
-- url     : https://prove2.me/theorems/00e622e1-a545-4c85-a727-b8b0afc1cb3e
-- title:
--   validate respects state equivalence
-- statement:
--   For `StateEquiv S T` and any block and clock reading, `validate` gives the same outcome on both (`invalid`, `futureTime`, `missingPrev`), or accepts both with `StateEquiv` results and the same undo data. The header path and `ContextualCheckBlock` read only the headers.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock, DisconnectBlock, UpdateCoins, ApplyTxInUndo, Chainstate::ConnectTip, Chainstate::DisconnectTip, Chainstate::ActivateBestChainStep, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CCoinsViewCache (coins.cpp)

import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

theorem BitcoinReorg.validate_equiv (S T : ChainState) (h : BitcoinReorg.StateEquiv S T) (b : BitcoinSer.Block) (now : Int) :
    (BitcoinBlockV2.validate S b now = .invalid ∧ BitcoinBlockV2.validate T b now = .invalid) ∨
    (BitcoinBlockV2.validate S b now = .futureTime ∧ BitcoinBlockV2.validate T b now = .futureTime) ∨
    (BitcoinBlockV2.validate S b now = .missingPrev ∧ BitcoinBlockV2.validate T b now = .missingPrev) ∨
    (∃ S' T' undo, BitcoinBlockV2.validate S b now = .accept S' undo ∧ BitcoinBlockV2.validate T b now = .accept T' undo ∧
      BitcoinReorg.StateEquiv S' T') := by sorry
