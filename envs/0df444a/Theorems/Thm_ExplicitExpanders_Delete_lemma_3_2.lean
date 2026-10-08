-- Prove2me | Theorems.Thm_ExplicitExpanders_Delete_lemma_3_2
-- name    : ExplicitExpanders.Delete.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:14:55.091978+00:00
-- url     : https://prove2.me/theorems/8d5f1725-7528-4611-b6e1-b61b889ecfb6
-- title:
--   Lemma 3.2 — eigenvectors of large eigenvalues do not decay on a cycle-free neighbourhood of an edge
-- statement:
--   Let $G=(V,E)$ be a finite $d$-regular graph with $d\ge 3$, let $uv$ be an edge of $G$, and let $r \ge 0$ be such that the $r$-neighbourhood of $uv$ contains no cycle. For $0\le i\le r$ let $N_i$ be the set of vertices at distance exactly $i$ from $\{u,v\}$ (so $N_0 = \{u,v\}$). Let $f \ne 0$ be an eigenvector of the adjacency matrix $A_G$ with eigenvalue $\mu \ge 2\sqrt{d-1}$. Then for every $1 \le i \le r$,
--   $$\sum_{w\in N_i} f^2(w) \;\ge\; \sum_{w\in N_{i-1}} f^2(w). \tag{7}$$
--
--   This is the delocalization statement of the paper: an eigenvector of a large eigenvalue cannot have its mass concentrated at an edge with a tree-like neighbourhood. It is applied to the edges of the added matching in the proof of Theorem 1.3.
--
--   **Formalization Note** The eigenvector condition is $A_G f = \mu f$ for the real adjacency matrix. This item is the lemma as printed ($\mu \ge 2\sqrt{d-1}$); the companion item `lemma_3_2_abs` states it for $|\mu| \ge 2\sqrt{d-1}$.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 11, Lemma 3.2 (inequality (7))

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods

namespace ExplicitExpanders.Delete

open Matrix

/-- Lemma 3.2 (Alon, arXiv:2003.11673v1, p. 11), as printed: eigenvalue `μ ≥ 2√(d-1)`. -/
theorem lemma_3_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d r : ℕ) (hd : 3 ≤ d) (hreg : G.IsRegularOfDegree d)
    (u v : V) (huv : G.Adj u v) (hcyc : NoCycleOn G (edgeBall G u v r))
    (f : V → ℝ) (μ : ℝ) (hf : f ≠ 0) (heig : G.adjMatrix ℝ *ᵥ f = μ • f)
    (hμ : 2 * Real.sqrt ((d : ℝ) - 1) ≤ μ) :
    ∀ i : ℕ, 1 ≤ i → i ≤ r →
      ∑ w ∈ layer G u v (i - 1), f w ^ 2 ≤ ∑ w ∈ layer G u v i, f w ^ 2 := by sorry

end ExplicitExpanders.Delete
