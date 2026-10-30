-- Prove2me | Theorems.Thm_BitcoinBackbone_common_prefix_private
-- name    : BitcoinBackbone.common_prefix_private
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:06:25.93582+00:00
-- url     : https://prove2.me/theorems/5a1b2fe5-f881-42f3-b0cf-275f74a1ce69
-- title:
--   A private fork loses (the core of Lemma 15)
-- statement:
--   For a legal, typical execution and honest party $p$ at round $r$: any valid chain $D$ of rounds $\le r$ that forks from an honest block of round $r_0$ (or from genesis) and is adversarial above the fork, with $r_0 + λ \le r$, is strictly shorter than `chain p r`.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765; Lemmas 7, 14, 15, Theorem 16, the chain-quality theorem; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockProof (chain.cpp) through the block mission's chainWork

import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.common_prefix_private (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (lam : ℕ) (hT : E.Typical lam) (p : ℕ) (hp : p < E.n) (r : ℕ)
    (D : BitcoinBackbone.Chain) (hD : E.ValidChain D) (hDr : ∀ B ∈ D, B.round ≤ r)
    (f r₀ : ℕ) (hfD : f ≤ D.length)
    (hfork : (f = 0 ∧ r₀ = 0) ∨
      ∃ q, ∃ hf : f - 1 < D.length, 0 < f ∧ D[f - 1] = BitcoinBackbone.Block.honest q r₀)
    (hadv : ∀ k (hk : k < D.length), f ≤ k → D[k].isHonest = false)
    (hwin : r₀ + lam ≤ r) : D.length < (E.chain p r).length := by sorry
