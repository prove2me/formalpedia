-- Prove2me | Theorems.Thm_CompOT_Auction_properties_b_c
-- name    : CompOT.Auction.properties_b_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:05.819474+00:00
-- url     : https://prove2.me/theorems/229adf5f-b75e-426a-b29e-d88bb7078fb4
-- title:
--   §3.7, properties (b)–(c), pp. 419–420 — each iteration keeps |S|, lowers one price by ≥ ε and raises none
-- statement:
--   Let $\mathbf C\in\mathbb R^{n\times n}$, $\varepsilon>0$, and let $(S^t,\xi^t,\mathbf g^t)_{t=0}^{T}$ be the first $T$ iterations of the auction algorithm started from $S^0=\emptyset$, $\mathbf g^0=0_n$. Then for every iteration $t<T$:
--
--   1. (b) the size of $S$ does not decrease: $|S^{t}|\le|S^{t+1}|$;
--   2. (c) some entry of the dual vector decreases by at least $\varepsilon$: there is an object $j$ with $\mathbf g^{t+1}_j\le\mathbf g^{t}_j-\varepsilon$;
--   3. no entry of the dual vector increases: $\mathbf g^{t+1}\le\mathbf g^{t}$ entrywise.
--
--   These are the bookkeeping properties the book reads off the update (3.9); the monotonicity of $\mathbf g$ is the fact "$\mathbf g^{\mathrm n}\le\mathbf g$" used in the proof of Proposition 3.7.
--
--   **Formalization Note** The book says the size of $S$ "can only increase"; it stays the same when the bidder displaces a previously assigned point, so (b) is stated as non-decrease. The book's (c) speaks of "an index $i$ such that $\mathbf g_i$ decreases"; $\mathbf g$ is indexed by objects, so the index is written $j$. Item 3 is from the proof of Proposition 3.7, p. 421.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §3.7, properties (b), (c), p. 419, and Algorithmic properties, p. 420; proof of Proposition 3.7, p. 421

import Mathlib
import Definitions.Def_CompOT_Auction_Defs

namespace CompOT.Auction

/-- Properties (b) and (c), p. 419, "valid after each iteration" (p. 420): along the auction
algorithm, the size of `S` never decreases, some entry of `g` decreases by at least `ε`, and no
entry of `g` increases (`g^n ≤ g`, proof of Proposition 3.7, p. 421). -/
theorem properties_b_c {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) {ε : ℝ} (hε : 0 < ε)
    (s : ℕ → AuctionState n) (T : ℕ) (hs : IsAuctionPrefix C ε s T) :
    ∀ t < T, (s t).S.card ≤ (s (t + 1)).S.card ∧
      (∃ j, (s (t + 1)).g j ≤ (s t).g j - ε) ∧
      ∀ j, (s (t + 1)).g j ≤ (s t).g j := by sorry

end CompOT.Auction
