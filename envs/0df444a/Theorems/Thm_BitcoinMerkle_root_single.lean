-- Prove2me | Theorems.Thm_BitcoinMerkle_root_single
-- name    : BitcoinMerkle.root_single
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:25:31.790217+00:00
-- url     : https://prove2.me/theorems/55dd19e5-dbae-4fce-899b-132203f29e55
-- title:
--   Merkle root of a single hash
-- statement:
--   For every $c$, $z$ and hash $a$, $\mathrm{computeMerkleRoot}_{c,z}([a]) = (a, \mathtt{false})$: a single hash is its own root and no level is processed, so the flag stays clear. In a block with only a coinbase, the Merkle root is the coinbase transaction id.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, ComputeMerkleRoot, src/consensus/merkle.cpp lines 51-73, with the CVE-2012-2459 comment at lines 16-50: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/merkle.cpp#L51

import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.root_single {H : Type} [DecidableEq H] (c : H → H → H) (z : H) (a : H) :
    BitcoinMerkle.computeMerkleRoot c z [a] = (a, false) := by sorry
