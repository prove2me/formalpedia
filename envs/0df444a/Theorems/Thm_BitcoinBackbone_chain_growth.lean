-- Prove2me | Theorems.Thm_BitcoinBackbone_chain_growth
-- name    : BitcoinBackbone.chain_growth
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:04:30.177782+00:00
-- url     : https://prove2.me/theorems/21a3b350-9e40-47a9-bc8f-b63f022fca9f
-- title:
--   Chain growth (Lemma 7): an honest chain grows by at least the successful rounds
-- statement:
--   For a legal execution, honest parties $p, q$ and rounds $r < s$: `(chain p r).length + ∑_{i ∈ [r+1, s)} X i ≤ (chain q s).length`. Every successful round adds a block to every honest party's chain by the next round.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765; Lemmas 7, 14, 15, Theorem 16, the chain-quality theorem; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockProof (chain.cpp) through the block mission's chainWork

import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.chain_growth (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (p q : ℕ) (hp : p < E.n) (hq : q < E.n) (r s : ℕ) (hrs : r < s) :
    (E.chain p r).length + ∑ i ∈ Finset.Ico (r + 1) s, E.X i ≤ (E.chain q s).length := by sorry
