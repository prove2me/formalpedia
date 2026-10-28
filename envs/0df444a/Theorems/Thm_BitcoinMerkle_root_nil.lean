-- Prove2me | Theorems.Thm_BitcoinMerkle_root_nil
-- name    : BitcoinMerkle.root_nil
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:25:20.281033+00:00
-- url     : https://prove2.me/theorems/5249778b-3881-4a72-af74-a716665a94a9
-- title:
--   Merkle root of no transactions
-- statement:
--   For every pairwise hash $c$ and zero hash $z$, $\mathrm{computeMerkleRoot}_{c,z}([\,]) = (z, \mathtt{false})$: the empty list yields the zero hash with the mutation flag clear, as `if (hashes.size() == 0) return uint256();`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, ComputeMerkleRoot, src/consensus/merkle.cpp lines 51-73, with the CVE-2012-2459 comment at lines 16-50: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/merkle.cpp#L51

import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.root_nil {H : Type} [DecidableEq H] (c : H → H → H) (z : H) :
    BitcoinMerkle.computeMerkleRoot c z [] = (z, false) := by sorry
