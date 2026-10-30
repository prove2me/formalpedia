-- Prove2me | Theorems.Thm_BitcoinUniqueness_chain_coinbases_distinct
-- name    : BitcoinUniqueness.chain_coinbases_distinct
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T13:48:25.773994+00:00
-- url     : https://prove2.me/theorems/b57ef2df-685c-4b17-8093-488953aa4170
-- title:
--   Along a post-BIP34 chain the coinbase scriptSigs are pairwise distinct
-- statement:
--   For a reachable state at next height $\ge 227{,}931$ and a chain `bs` connected to it (`connectChain`) staying below height $2^{31}$: the list of coinbase `scriptSig`s of the blocks of `bs` has no duplicates. Hence no two post-BIP34 blocks of one chain have the same coinbase *transaction* — the structural half of the argument that lets `ConnectBlock` skip the BIP30 scan. What this does not establish, and the model cannot: that two different transactions never share a txid (collision resistance of SHA-256d), and that no pre-BIP34 coinbase `scriptSig` happens to start with a height push of a height below 1,983,702 (a fact about the historical chain's data, which is why Core re-enables the scan from that height).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock (fEnforceBIP30, BIP34_IMPLIES_BIP30_LIMIT), ContextualCheckBlock (the BIP34 height push), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CScript::push_int64, CScriptNum::serialize (script/script.h); BIP30, BIP34

import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinHeader
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinReorg
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem BitcoinUniqueness.chain_coinbases_distinct (S : ChainState) (hR : BitcoinBlockV2.Reachable S)
    (h34 : BitcoinHeader.BIP34Height ≤ S.nextHeight) (bs : List (BitcoinSer.Block × Int)) (T : ChainState)
    (undos : List BlockUndo) (hc : BitcoinReorg.connectChain S bs = some (T, undos))
    (hlt : S.nextHeight + bs.length < 2 ^ 31) :
    (bs.map fun p => BitcoinUniqueness.coinbaseScriptSig p.1).Nodup := by sorry
