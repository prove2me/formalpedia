-- Prove2me | Theorems.Thm_BitcoinMerkle_root_pair
-- name    : BitcoinMerkle.root_pair
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:25:42.357917+00:00
-- url     : https://prove2.me/theorems/dfa71295-fc5a-4cda-9347-65fa8105c9fa
-- title:
--   Merkle root of two hashes
-- statement:
--   For every $c$, $z$ and hashes $a, b$, $\mathrm{computeMerkleRoot}_{c,z}([a, b]) = (c(a, b),\ [a = b])$: one level is processed, producing $c(a,b)$, and the flag is set exactly when the two leaves are equal. This is the smallest instance of the mutation check.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, ComputeMerkleRoot, src/consensus/merkle.cpp lines 51-73, with the CVE-2012-2459 comment at lines 16-50: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/merkle.cpp#L51

import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.root_pair {H : Type} [DecidableEq H] (c : H → H → H) (z : H) (a b : H) :
    BitcoinMerkle.computeMerkleRoot c z [a, b] = (c a b, decide (a = b)) := by sorry
