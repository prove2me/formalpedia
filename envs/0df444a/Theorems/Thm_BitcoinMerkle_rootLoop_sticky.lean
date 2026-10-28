-- Prove2me | Theorems.Thm_BitcoinMerkle_rootLoop_sticky
-- name    : BitcoinMerkle.rootLoop_sticky
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:26:01.951734+00:00
-- url     : https://prove2.me/theorems/71b3c993-5d96-4ab5-8f22-5fbf1b8c37c0
-- title:
--   Once set, the mutation flag stays set
-- statement:
--   For every $c$, $z$ and list $\ell$, $\mathrm{rootLoop}_{c,z}(\ell, \mathtt{true}).2 = \mathtt{true}$: the flag is only ever combined with further tests by disjunction, so a mutation detected at one level is reported at the end regardless of what later levels contain.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, ComputeMerkleRoot, src/consensus/merkle.cpp lines 51-73, with the CVE-2012-2459 comment at lines 16-50: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/merkle.cpp#L51

import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.rootLoop_sticky {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) : (BitcoinMerkle.rootLoop c z hs true).2 = true := by sorry
