-- Prove2me | Theorems.Thm_BitcoinBackbone_chain_quality
-- name    : BitcoinBackbone.chain_quality
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:08:07.534092+00:00
-- url     : https://prove2.me/theorems/ffbeb40e-8d16-4584-98d5-ca94d63dec2e
-- title:
--   Chain quality: every λ consecutive blocks of an honest chain contain an honest block
-- statement:
--   For a legal, typical execution, honest $p$, round $r$ and position $u$ with $u + λ \le$ `(chain p r).length`: among the $λ$ blocks of `chain p r` starting at position $u$ there is an honest one. The weak ($μ > 0$) form of the paper's chain-quality theorem.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765; Lemmas 7, 14, 15, Theorem 16, the chain-quality theorem; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockProof (chain.cpp) through the block mission's chainWork

import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.chain_quality (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (lam : ℕ) (hT : E.Typical lam) (p : ℕ) (hp : p < E.n) (r u : ℕ)
    (hu : u + lam ≤ (E.chain p r).length) :
    ∃ B ∈ ((E.chain p r).drop u).take lam, B.isHonest = true := by sorry
