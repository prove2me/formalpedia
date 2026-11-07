-- Prove2me | Theorems.Thm_DetCCHard_lemma_6_7
-- name    : DetCCHard.lemma_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:35:10.545877+00:00
-- url     : https://prove2.me/theorems/8db476e0-882b-4c15-ac49-1acd6142a655
-- title:
--   Lemma 6.7 — Kraft count over an antichain of protocol nodes
-- statement:
--   Let $q = 2^k$ be a power of two, and let $V$ be a set of nodes of a binary protocol tree, none an ancestor of another, all at depth at most $\log q$. For $v \in V$ at depth $r_v$ put $\kappa_v = q\,2^{-r_v}$. Suppose each node $v \in V$ holds $h_v$ objects, $z_v \le h_v$ of them marked, and
--   $$
--   \sum_{v \in V} (h_v + z_v) > q .
--   $$
--   Then some $v$ has $h_v + z_v > \kappa_v$. For this $v$, if $\kappa_v \ge 2$ then $h_v \ge \kappa_v/2 + 1$, and if $\kappa_v = 1$ then $h_v \ge 2$ or $h_v = z_v = 1$.
--
--   The count locates a stopping node that holds too many tracked input sets, which is where the collision argument finds its contradiction.
--
--   **Formalization Note** Nodes are words of bits (the transcript leading to them); the depth is the word length and "ancestor" is "proper prefix". $\kappa_v = q / 2^{r_v}$ is a natural number.
--
--   Differences from the source:
--   - encoding: nodes of a binary protocol tree → arbitrary words of bits, ancestry as proper prefix; reason: every word is a node of the complete binary tree and every protocol tree's nodes are words; the hypotheses and conclusion only use depths and ancestry
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Lemma 6.7, p.23

import Mathlib

namespace DetCCHard

/-- **Lemma 6.7 (Kraft count)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256
ad552d13…a4a03, Lemma 6.7, p.23). Let `q = 2^k` be a power of two and `V` a set of nodes of a
binary protocol tree, none an ancestor of another, all at depth at most `log q = k`. For `v ∈ V`
at depth `r_v` put `κ_v = q 2^{-r_v}`. Suppose each node `v ∈ V` holds `h_v` objects, `z_v ≤ h_v`
of them marked, and `∑_{v ∈ V} (h_v + z_v) > q`. Then some `v` has `h_v + z_v > κ_v`, and for this
`v`: if `κ_v ≥ 2` then `h_v ≥ κ_v/2 + 1`, and if `κ_v = 1` then `h_v ≥ 2` or `h_v = z_v = 1`.

**Formalization Note** A node is the word of bits leading to it from the root, its depth is the
word's length, and `v` is an ancestor of `w` when `v` is a proper prefix of `w`. Every word is a
node of the complete binary tree, so the statement covers the nodes of every protocol tree.
`κ_v = q / 2^{r_v}` is a natural number since `r_v ≤ k`. -/
theorem lemma_6_7 (k q : ℕ) (hq : q = 2 ^ k) (V : Finset (List Bool))
    (hV : ∀ v ∈ V, ∀ w ∈ V, v <+: w → v = w) (hdepth : ∀ v ∈ V, v.length ≤ k)
    (h z : List Bool → ℕ) (hz : ∀ v ∈ V, z v ≤ h v) (hsum : q < ∑ v ∈ V, (h v + z v)) :
    ∃ v ∈ V, q / 2 ^ v.length < h v + z v ∧
      (2 ≤ q / 2 ^ v.length → q / 2 ^ v.length / 2 + 1 ≤ h v) ∧
      (q / 2 ^ v.length = 1 → 2 ≤ h v ∨ (h v = 1 ∧ z v = 1)) := by sorry

end DetCCHard
