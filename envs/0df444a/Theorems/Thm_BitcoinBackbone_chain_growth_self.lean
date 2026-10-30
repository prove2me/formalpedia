-- Prove2me | Theorems.Thm_BitcoinBackbone_chain_growth_self
-- name    : BitcoinBackbone.chain_growth_self
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:05:15.321209+00:00
-- url     : https://prove2.me/theorems/41167189-5780-457e-8d31-b14a82063437
-- title:
--   Chain growth for one party
-- statement:
--   The same bound with $q = p$ and $r \le s$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765; Lemmas 7, 14, 15, Theorem 16, the chain-quality theorem; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockProof (chain.cpp) through the block mission's chainWork

import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.chain_growth_self (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (p : ℕ) (hp : p < E.n) (r s : ℕ) (hrs : r ≤ s) :
    (E.chain p r).length + ∑ i ∈ Finset.Ico (r + 1) s, E.X i ≤ (E.chain p s).length := by sorry
