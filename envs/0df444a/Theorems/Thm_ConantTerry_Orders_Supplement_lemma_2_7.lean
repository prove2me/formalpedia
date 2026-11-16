-- Prove2me | Theorems.Thm_ConantTerry_Orders_Supplement_lemma_2_7
-- name    : ConantTerry.Orders.Supplement.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:25:00.822315+00:00
-- url     : https://prove2.me/theorems/c1fcf29e-26f9-4809-9442-669461279c56
-- title:
--   Lemma 2.7 — Ramsey for proper tree embeddings
-- statement:
--   Let $m\ge1$ and $t,t_1,\ldots,t_m\ge0$ be integers with $t=\sum_{i=1}^m t_i$. Write $B_s$ for the binary words of length $s$ and $B_{\le s}$ for the words of length at most $s$. For every cover $B_t=\bigcup_{i=1}^m C_i$, there are $i\in\{1,\ldots,m\}$ and a proper oriented tree embedding
--   $$
--   \phi:B_{\le t_i}\longrightarrow B_{\le t},\qquad \phi(B_{t_i})\subseteq C_i.
--   $$
--   An embedding preserves the appended branch bit: whenever $\sigma a$ is a prefix of $\tau$, $\phi(\sigma)a$ is a prefix of $\phi(\tau)$. Properness sends the last level to the last level, without fixing the root or intermediate levels. Only the images of last-level leaves must be in $C_i$; internal nodes need not have that color. Overlaps and empty color classes are allowed, and all zero-height cases are retained.
--
--   This is the leaf-coloring tool used by Theorems 1.14 and 5.2, distinct from the base mission's node-coloring Lemma 2.6.
--
--   Differences from the source:
--   - encoding: finite binary words and 1-based finite indices → published List Bool word subtypes and zero-based Fin indices; reason: length, prefix, orientation and index inequalities are preserved by relabeling
--   - encoding: φ(B_{t_i}) is contained in C_i → each leaf image equals the canonical inclusion of a leaf ν belonging to C_i; reason: the existential leaf witness expresses the same image containment without a partial cast
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p. 9, Lemma 2.7; proof pp. 9

import Mathlib
import Definitions.Def_ConantTerry_Orders_tree_embeddings

namespace ConantTerry.Orders.Supplement

/-- Lemma 2.7, p.9. Only final-level leaves are colored. Heights may be zero;
properness is the published oriented embedding predicate. -/
theorem lemma_2_7 (m t : ℕ) (hm : 1 ≤ m) (heights : Fin m → ℕ)
    (ht : t = ∑ i, heights i) (C : Fin m → Set (WordsAt t))
    (hcover : ∀ η : WordsAt t, ∃ i : Fin m, η ∈ C i) :
    ∃ (i : Fin m) (φ : WordsAtMost (heights i) → WordsAtMost t),
      IsProperEmbedding φ ∧
        ∀ η : WordsAt (heights i), ∃ ν ∈ C i,
          φ (leafInclusion η) = leafInclusion ν := by sorry

end ConantTerry.Orders.Supplement
