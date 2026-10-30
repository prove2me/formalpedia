-- Prove2me | Theorems.Thm_BitcoinBackbone_common_prefix_rounds
-- name    : BitcoinBackbone.common_prefix_rounds
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:06:58.882659+00:00
-- url     : https://prove2.me/theorems/5d56935b-90f3-40c4-8b0f-d15a9029765f
-- title:
--   Common prefix, round form (Lemma 15 and Theorem 16)
-- statement:
--   For a legal, typical execution, honest $p_1, p_2$, rounds $r_1 \le r_2$ and a window $λ \le w \le r_1$: the blocks of `chain p₁ r₁` of round $\le r_1 - w$ form a prefix of `chain p₂ r₂`.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765; Lemmas 7, 14, 15, Theorem 16, the chain-quality theorem; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockProof (chain.cpp) through the block mission's chainWork

import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.common_prefix_rounds (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (lam : ℕ) (hT : E.Typical lam) (p₁ p₂ : ℕ) (hp₁ : p₁ < E.n) (hp₂ : p₂ < E.n)
    (r₁ r₂ : ℕ) (hr : r₁ ≤ r₂) (w : ℕ) (hw : lam ≤ w) (hwr : w ≤ r₁) :
    (E.chain p₁ r₁).upTo (r₁ - w) <+: E.chain p₂ r₂ := by sorry
