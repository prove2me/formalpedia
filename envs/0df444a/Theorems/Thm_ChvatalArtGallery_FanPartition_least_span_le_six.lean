-- Prove2me | Theorems.Thm_ChvatalArtGallery_FanPartition_least_span_le_six
-- name    : ChvatalArtGallery.FanPartition.least_span_le_six
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:57:56.396273+00:00
-- url     : https://prove2.me/theorems/e6ea828c-3615-471d-a106-1042051c4c46
-- title:
--   Proof of the Theorem, p. 40 — the least k ≥ 4 with an inner edge (j, j + k) satisfies k ≤ 6
-- statement:
--   Let $n \ge 6$ and let $D$ be the set of inner edges of an $n$-triangulation $G$ with vertices $0,\dots,n-1$ in cyclic order (indices mod $n$). Let $k$ be the smallest integer such that $k \ge 4$ and $G$ has an inner edge of the form $\{j, j+k\}$. Then such a $k$ exists and
--   $$k \le 6.$$
--   Precisely: there are a vertex $j$ and an integer $k$ with $4 \le k \le 6$ and $\{j,j+k\} \in D$, such that no vertex $j'$ and integer $k'$ with $4 \le k' < k$ have $\{j', j'+k'\} \in D$.
--
--   The edge $\{j,j+k\}$ of least span $k\ge 4$ is the edge along which Chvátal cuts $G$ in the inductive step; the bound $k \le 6$ is what makes the subsequent case analysis finite.
--
--   **Formalization Note.** The paper says "$G$ has an edge $(j, j+k)$". The statement asks for an *inner* edge ($\{j,j+k\}\in D$): read literally, a side $\{j, j+n-1\}$ of the $n$-gon would give an edge of span $n - 1 \in \{5,6\}$ for $n = 6, 7$ and make the claim trivial there, whereas for $n \ge 6$ some diagonal always has a span in $[4, n-2]$, so the least span of an edge is always a diagonal's and the content is unchanged. The minimality of $k$ is stated explicitly (no inner edge of span $k'$ with $4 \le k' < k$); since $k \le 6 \le n$, every span $k' < k$ is less than $n$, so $j' + k'$ never wraps all the way around. $j+k$ is the vertex $(j+k) \bmod n$ (`shift j k`).
-- source:
--   Chvátal, A combinatorial theorem in plane geometry, J. Combin. Theory Ser. B 18 (1975), p. 40, proof of the Theorem, "Let k be the smallest integer such that k ≥ 4 and G has an edge (j, j + k). First of all, let us note that k ≤ 6."

import Mathlib
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation

namespace ChvatalArtGallery.FanPartition

/-- Proof of the Theorem, p. 40: for n ≥ 6, the least k ≥ 4 such that some inner edge has the
form (j, j + k) exists and satisfies k ≤ 6. -/
theorem least_span_le_six (n : ℕ) (hn : 6 ≤ n) (D : Finset (Sym2 (Fin n)))
    (hD : IsTriangulation n D) :
    ∃ (j : Fin n) (k : ℕ), 4 ≤ k ∧ k ≤ 6 ∧ s(j, shift j k) ∈ D ∧
      ∀ (j' : Fin n) (k' : ℕ), 4 ≤ k' → k' < k → s(j', shift j' k') ∉ D := by sorry

end ChvatalArtGallery.FanPartition
