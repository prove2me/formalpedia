-- Prove2me | Theorems.Thm_CompOT_Auction_proposition_3_7
-- name    : CompOT.Auction.proposition_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:58.885625+00:00
-- url     : https://prove2.me/theorems/5f5afa8a-b77a-48d8-92f9-a03ff64ea249
-- title:
--   Proposition 3.7, p. 420 — the auction algorithm maintains ε-complementary slackness at each iteration
-- statement:
--   Let $\mathbf C\in\mathbb R^{n\times n}$ and $\varepsilon>0$, and let $(S^t,\xi^t,\mathbf g^t)_{t=0}^{T}$ be the first $T$ iterations of the auction algorithm started from $S^0=\emptyset$, $\mathbf g^0=0_n$. Then every state satisfies ε-complementary slackness: for all $t\le T$,
--   $$
--   \forall i\in S^t,\qquad \mathbf C_{i,\xi^t_i}-\mathbf g^t_{\xi^t_i}\le\varepsilon+\min_j\big(\mathbf C_{i,j}-\mathbf g^t_j\big).
--   $$
--
--   Together with termination, this invariant is what makes the final assignment $n\varepsilon$-suboptimal (Proposition 3.9).
--
--   **Formalization Note** $[\![n]\!]$ is `Fin n`; the iterations are any sequence of admissible updates (3.9), ties in the argmins being resolved arbitrarily.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 3.7, p. 420

import Mathlib
import Definitions.Def_CompOT_Auction_Defs

namespace CompOT.Auction

/-- Proposition 3.7, p. 420: the auction algorithm maintains ε-complementary slackness at each
iteration. -/
theorem proposition_3_7 {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) {ε : ℝ} (hε : 0 < ε)
    (s : ℕ → AuctionState n) (T : ℕ) (hs : IsAuctionPrefix C ε s T) :
    ∀ t ≤ T, EpsCS C ε (s t) := by sorry

end CompOT.Auction
