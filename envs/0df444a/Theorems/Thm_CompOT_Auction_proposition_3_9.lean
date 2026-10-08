-- Prove2me | Theorems.Thm_CompOT_Auction_proposition_3_9
-- name    : CompOT.Auction.proposition_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:38.275806+00:00
-- url     : https://prove2.me/theorems/2208c448-4194-43db-b9e7-965af8bd1d04
-- title:
--   Proposition 3.9, p. 422 — on termination the auction algorithm returns an assignment whose cost is nε suboptimal
-- statement:
--   Let $n\ge2$, $\mathbf C\in\mathbb R^{n\times n}$ and $\varepsilon>0$. Run the auction algorithm from $S=\emptyset$, $\mathbf g=0_n$ until it terminates, i.e. until $S=[\![n]\!]$, and let $\xi$ be the final assignment vector. Then $\xi$ is a permutation of $[\![n]\!]$, and its cost is within $n\varepsilon$ of the optimum:
--   $$
--   \sum_i \mathbf C_{i,\xi_i}\;\le\;\sum_i\mathbf C_{i,\sigma_i}+n\varepsilon\qquad\text{for every permutation }\sigma .
--   $$
--
--   This is the accuracy guarantee of the auction algorithm. In particular, if $\mathbf C$ has integer entries and $n\varepsilon<1$, the returned assignment is optimal.
--
--   **Formalization Note** The statement concerns every terminated run: any number $T$ of admissible iterations (3.9), with ties resolved arbitrarily, that ends with $S=[\![n]\!]$; it does not assert that the algorithm terminates (that is Proposition 3.8). The cost is the unnormalized sum $\sum_i\mathbf C_{i,\sigma_i}$, as in the book's proof ($t^\star=\sum\mathbf C_{i,\sigma_i}$); with the $\frac1n$ normalization of (2.2) the gap would read $\varepsilon$. The hypothesis $n\ge2$ is the range where the update (3.9) is defined: it needs a second-best index $j^2_i\ne j^1_i$ (for $n=1$ no iteration exists and the algorithm never terminates). That the final $\xi$ is a permutation is part of the conclusion, as the book asserts ("$S$ grows to cover $[\![n]\!]$ as $\xi$ describes a permutation").
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 3.9, p. 422

import Mathlib
import Definitions.Def_CompOT_Auction_Defs

namespace CompOT.Auction

/-- Proposition 3.9, p. 422: the auction algorithm finds an assignment whose cost is `nε`
suboptimal. On termination (`S = ⟦n⟧`) the partial assignment `ξ` is a permutation and
`∑ᵢ C_{i,ξ_i} ≤ ∑ᵢ C_{i,σ_i} + nε` for every permutation `σ`. -/
theorem proposition_3_9 {n : ℕ} (hn : 2 ≤ n) (C : Matrix (Fin n) (Fin n) ℝ) {ε : ℝ}
    (hε : 0 < ε) (s : ℕ → AuctionState n) (T : ℕ) (hs : IsAuctionRun C ε s T) :
    Function.Bijective (s T).ξ ∧
      ∀ σ : Equiv.Perm (Fin n), assignmentCost C (s T).ξ ≤ assignmentCost C σ + n * ε := by sorry

end CompOT.Auction
