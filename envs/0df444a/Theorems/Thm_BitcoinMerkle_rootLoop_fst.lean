-- Prove2me | Theorems.Thm_BitcoinMerkle_rootLoop_fst
-- name    : BitcoinMerkle.rootLoop_fst
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:25:51.20998+00:00
-- url     : https://prove2.me/theorems/561f5b90-64d6-4f21-a0f7-1f3859fae4b6
-- title:
--   The root does not depend on the incoming flag
-- statement:
--   For every $c$, $z$, list $\ell$ and flags $m, m'$, the first components agree: $\mathrm{rootLoop}_{c,z}(\ell, m).1 = \mathrm{rootLoop}_{c,z}(\ell, m').1$. The mutation flag is carried alongside the computation and never influences which hashes are produced.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, ComputeMerkleRoot, src/consensus/merkle.cpp lines 51-73, with the CVE-2012-2459 comment at lines 16-50: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/merkle.cpp#L51

import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.rootLoop_fst {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) (m m' : Bool) : (BitcoinMerkle.rootLoop c z hs m).1 = (BitcoinMerkle.rootLoop c z hs m').1 := by sorry
