-- Prove2me | Theorems.Thm_BrouwerLaplacian_eq_5_3
-- name    : BrouwerLaplacian.eq_5_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T17:00:10.972939+00:00
-- url     : https://prove2.me/theorems/ed74cf30-a79c-4ee1-b152-133766678290
-- title:
--   Identity (5.3) — $\sum_{i\in K}v_i+\sum_{i\in K}\sum_{j\notin K}|M_{ij}|=-\operatorname{tr}((L_{G_K}-rC)N)$
-- statement:
--   Let $P$ be a real $n\times n$ orthogonal projection of rank $k$ with $P\mathbf 1=0$, with $M$, $v=CM\mathbf 1$ and $N=CMC$ as in Lemma 5.5. Let $K\subseteq[n]$ with $1\le r=|K|\le n-1$, and let $G_K$ be the split graph with clique $K$, independent set $K^{\mathrm c}$, and an edge between $i\in K$ and $j\notin K$ exactly when $M_{ij}\ge 0$. Then
--
--   $$\sum_{i\in K}v_i+\sum_{i\in K}\sum_{j\notin K}|M_{ij}|=-\operatorname{tr}\big((L_{G_K}-rC)N\big).$$
--
--   The paper states this for the prefix $K=\{1,\dots,r\}$ after sorting the coordinates of a test vector $x$. Combined with Lemma 3.2 and $\|N\|\le1$ it gives the level-cut inequality (5.4).
--
--   **Formalization Note** $G_K$ is `splitGraphOf (routingM P) K`; its Laplacian is Mathlib's `lapMatrix`.
--
--   Differences from the source:
--   - generalization: the prefix $\{1,\dots,r\}$ → any vertex set $K$ with $|K|=r$; reason: the paper's prefix is the instance $K=\{1,\dots,r\}$, and the identity is invariant under relabeling the coordinates
--   - encoding: cross edge "wherever $M_{ij}\ge 0$" → $A_{ij}\ge 0$ read with $i$ the endpoint in $K$; reason: $M$ is symmetric, so this is the same graph
--   - encoding: indices $1,\dots,n$ → $\mathrm{Fin}\,n=\{0,\dots,n-1\}$; reason: relabeling; same instances
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, §5, proof of Lemma 5.5, p.7, eq. (5.3)

import Mathlib
import Definitions.Def_BrouwerLaplacian_centering
import Definitions.Def_BrouwerLaplacian_IsOrthProj
import Definitions.Def_BrouwerLaplacian_routingM
import Definitions.Def_BrouwerLaplacian_splitGraphOf

namespace BrouwerLaplacian

open Finset Matrix

/-- **Identity (5.3).**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, §5, proof of
Lemma 5.5, p.7, eq. (5.3): "For each 1 ≤ r ≤ n − 1, let Gᵣ be the split graph on [n] obtained
by making {1, 2, . . . , r} a clique, {r + 1, . . . , n} an independent set, and adding an edge
across the cut wherever Mᵢⱼ ≥ 0. We first prove the identity
Σᵢ₌₁ʳ vᵢ + Σᵢ₌₁ʳ Σⱼ₌ᵣ₊₁ⁿ |Mᵢⱼ| = −tr((L_{Gᵣ} − rC)N)."

Let `P` be an orthogonal projection of rank `k` with `P𝟙 = 0`, with `M`, `v = CM𝟙` and
`N = CMC` as in Lemma 5.5. For every vertex set `K` with `1 ≤ |K| = r ≤ n − 1`, let `G_K` be
the split graph with clique `K`, independent set `Kᶜ`, and a cross edge `{i, j}` (`i ∈ K`,
`j ∉ K`) exactly when `Mᵢⱼ ≥ 0`. Then
`Σ_{i∈K} vᵢ + Σ_{i∈K} Σ_{j∉K} |Mᵢⱼ| = −tr((L_{G_K} − rC)N)`.

**Formalization Note.** The paper takes the prefix `K = {1, …, r}` after sorting the
coordinates; here `K` is any set of size `r` (the prefix is one instance). `G_K` is
`splitGraphOf (routingM P) K`. -/
theorem eq_5_3 {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) (K : Finset (Fin n)) (hK1 : 1 ≤ #K) (hKn : #K ≤ n - 1) :
    ∑ i ∈ K, routingV P i + ∑ i ∈ K, ∑ j ∈ Kᶜ, |routingM P i j|
      = -Matrix.trace (((splitGraphOf (routingM P) K).lapMatrix ℝ - (#K : ℝ) • centering n)
          * routingN P) := by sorry

end BrouwerLaplacian
