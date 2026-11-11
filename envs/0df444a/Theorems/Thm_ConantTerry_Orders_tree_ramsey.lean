-- Prove2me | Theorems.Thm_ConantTerry_Orders_tree_ramsey
-- name    : ConantTerry.Orders.tree_ramsey
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:32:31.771637+00:00
-- url     : https://prove2.me/theorems/e669b7fa-eb57-4a3e-8de7-6b5608ba6004
-- title:
--   Lemma 2.6 — Ramsey for tree embeddings
-- statement:
--   Let $m,t\ge1$ and $t_1,\ldots,t_m\ge1$ be integers satisfying
--   $$
--   t=t_1+\cdots+t_m-m+1.
--   $$
--   For any cover $B_{<t}=C_1\cup\cdots\cup C_m$, there exist $i\in[m]$ and a tree embedding $\phi:B_{<t_i}\to B_{<t}$ such that
--   $$
--   \operatorname{range}(\phi)\subseteq C_i.
--   $$
--   The cover need not be disjoint; empty parts are allowed. The embedding need not fix the root or preserve levels, and its target height can differ from its source height. This is the node-cover result used in the main extraction argument.
--
--   Differences from the source:
--   - encoding: binary words in B_<t, B_≤t and B_t → length-constrained subtypes of List Bool, with false = 0 and true = 1; reason: the empty word, concatenation and initial-segment order are preserved exactly
--   - encoding: [n] = {1,...,n} → Fin n = {0,...,n-1}; reason: subtracting one from every index preserves the order and all diagonal conventions
--   - encoding: t = sum_i t_i - m + 1 → t + m = sum_i t_i + 1; reason: every t_i is positive and there are m of them, so the rearrangement is equivalent and avoids truncated natural subtraction
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p.8, Lemma 2.6 (proof pp.8–9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1299.pdf

import Mathlib
import Definitions.Def_ConantTerry_Orders_tree_embeddings

namespace ConantTerry.Orders

/-- Lemma 2.6, p.8. A cover may overlap and may contain empty parts.
The height equation is rearranged to avoid natural subtraction. -/
theorem tree_ramsey (m t : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t)
    (heights : Fin m → ℕ) (hpos : ∀ i, 1 ≤ heights i)
    (hsum : t + m = (∑ i : Fin m, heights i) + 1)
    (C : Fin m → Set (WordsBelow t))
    (hcover : ∀ σ : WordsBelow t, ∃ i : Fin m, σ ∈ C i) :
    ∃ (i : Fin m) (φ : WordsBelow (heights i) → WordsBelow t),
      IsTreeEmbedding φ ∧ Set.range φ ⊆ C i := by sorry

end ConantTerry.Orders
