-- Prove2me | Theorems.Thm_BitcoinBackbone_chainWork_const_bits
-- name    : BitcoinBackbone.chainWork_const_bits
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:03:55.459445+00:00
-- url     : https://prove2.me/theorems/85e6ac9c-8a97-40e1-8d5e-2d4e9310c20f
-- title:
--   At constant difficulty, Core's chain work is the number of blocks times one block's proof
-- statement:
--   For a block-mission chain state all of whose headers carry the same `bits`: `S.chainWork = S.headers.length * blockProof bits`. The link between the paper's "length" and Core's `nChainWork`.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765; Lemmas 7, 14, 15, Theorem 16, the chain-quality theorem; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockProof (chain.cpp) through the block mission's chainWork

import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.chainWork_const_bits (S : BitcoinBlockV2.ChainState) (bits : ℕ)
    (h : ∀ hd ∈ S.headers, hd.bits = bits) :
    S.chainWork = S.headers.length * BitcoinBlockV2.blockProof bits := by sorry
