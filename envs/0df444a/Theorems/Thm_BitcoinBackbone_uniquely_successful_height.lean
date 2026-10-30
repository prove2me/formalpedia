-- Prove2me | Theorems.Thm_BitcoinBackbone_uniquely_successful_height
-- name    : BitcoinBackbone.uniquely_successful_height
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:05:49.478326+00:00
-- url     : https://prove2.me/theorems/bd42588e-292f-4903-be71-27f2a6560c9b
-- title:
--   A uniquely successful round pins the honest block at its height (Lemma 14)
-- statement:
--   If round $i$ is uniquely successful with honest miner $m$, then in any valid chain the block at height `(base m i).length` (0-based index), if honest, is $m$'s block of round $i$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765; Lemmas 7, 14, 15, Theorem 16, the chain-quality theorem; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockProof (chain.cpp) through the block mission's chainWork

import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.uniquely_successful_height (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (i m : ℕ) (hm : m < E.n) (hmi : E.mined m i = true) (hY : E.Y i = 1)
    (C : BitcoinBackbone.Chain) (hC : E.ValidChain C) (t : ℕ) (ht : t < C.length)
    (hti : t = (E.base m i).length) (q s : ℕ) (h : C[t] = BitcoinBackbone.Block.honest q s) :
    q = m ∧ s = i := by sorry
