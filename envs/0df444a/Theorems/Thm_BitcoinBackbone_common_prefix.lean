-- Prove2me | Theorems.Thm_BitcoinBackbone_common_prefix
-- name    : BitcoinBackbone.common_prefix
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:07:28.372215+00:00
-- url     : https://prove2.me/theorems/9808ed9d-726e-4904-80c6-318788a201e5
-- title:
--   Common prefix (Theorem 16): dropping 2λ blocks gives a prefix of every later honest chain
-- statement:
--   For a legal, typical execution, honest $p_1, p_2$ and rounds $r_1 \le r_2$: `(chain p₁ r₁).take ((chain p₁ r₁).length - 2λ)` is a prefix of `chain p₂ r₂`. The paper's $k = 2λf$ becomes $2λ$ here.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765; Lemmas 7, 14, 15, Theorem 16, the chain-quality theorem; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockProof (chain.cpp) through the block mission's chainWork

import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.common_prefix (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (lam : ℕ) (hT : E.Typical lam) (p₁ p₂ : ℕ) (hp₁ : p₁ < E.n) (hp₂ : p₂ < E.n)
    (r₁ r₂ : ℕ) (hr : r₁ ≤ r₂) :
    (E.chain p₁ r₁).take ((E.chain p₁ r₁).length - 2 * lam) <+: E.chain p₂ r₂ := by sorry
