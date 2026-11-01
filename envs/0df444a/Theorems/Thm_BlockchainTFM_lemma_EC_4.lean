-- Prove2me | Theorems.Thm_BlockchainTFM_lemma_EC_4
-- name    : BlockchainTFM.lemma_EC_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:02:38.240798+00:00
-- url     : https://prove2.me/theorems/2f42e73f-d183-4020-968d-be0ba3da8b3a
-- title:
--   Lemma EC.4: adding an item to weighted sampling without replacement does not raise any existing item's inclusion probability
-- statement:
--   In a weighted random sampling without replacement, if we add a new item, the probability that any already existing item is chosen does not increase.
--
--   Precisely: let $n+1$ items carry positive weights $w_1,\dots,w_{n+1}$, the last one being the new item, and run $k$ rounds of weighted sampling without replacement. For every existing item $i\le n$,
--   $$\Pr\bigl[i\ \text{drawn among items }1,\dots,n+1\bigr]\ \le\ \Pr\bigl[i\ \text{drawn among items }1,\dots,n\bigr],$$
--   the right-hand side computed with the same weights $w_1,\dots,w_n$.
--
--   In Mechanism 3 a fake bid is a new item, so a fake bid can only lower each real user's allocation; this gives Proposition EC.1 and the U-SP clause of Theorem 4.
--
--   **Formalization Note** The inclusion probabilities are those of (23)–(25). The new item is placed last, which loses no generality because the sampling law does not depend on the labels.
--
--   Differences from the source:
--   - encoding: a new item among n existing ones → weights w : Fin (n+1) → ℝ, positive, new item Fin.last n, existing item i as Fin.castSucc i; reason: Lean convention; relabelling does not change the sampling law
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, Appendix EC.4.4.3, Lemma EC.4, p.ec24

import Mathlib
import Definitions.Def_BlockchainTFM_Sampling

namespace BlockchainTFM

/-- **Lemma EC.4**, Chen–Simchi-Levi–Zhao–Zhou, arXiv:2209.13099v7, p.ec24. In a weighted random
sampling without replacement, if we add a new item, the probability that any already existing
item is chosen does not increase.

For every number of rounds `k`, positive weights `w` on `n + 1` items (the new item is the last
one, `Fin.last n`) and every existing item `i`, the probability that `i` is drawn in `k` rounds
among all `n + 1` items is at most its probability of being drawn among the first `n` items
with the same weights.

**Formalization Note.** Existing item `i : Fin n` is `Fin.castSucc i` among the `n + 1` items;
the inclusion probability is `inclProb` ((23)–(25)). Placing the new item last loses no
generality: the sampling law is invariant under relabelling. -/
theorem lemma_EC_4 {n : ℕ} (k : ℕ) (w : Fin (n + 1) → ℝ) (hw : ∀ j, 0 < w j) (i : Fin n) :
    inclProb k w (Fin.castSucc i) ≤ inclProb k (fun j : Fin n => w (Fin.castSucc j)) i := by sorry

end BlockchainTFM
