-- Prove2me | Theorems.Thm_EvenCycleTuran_OddGirthOdd_claim_19
-- name    : EvenCycleTuran.OddGirthOdd.claim_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:26:37.177565+00:00
-- url     : https://prove2.me/theorems/488d3627-6ea4-4983-ab73-29f2ae0e4342
-- title:
--   Claim 19, p. 29 — the number of edges inside N_l(v) is O(|N_l(v)|) = O(n)
-- statement:
--   Let $k > l \ge 2$. There is a constant $C = C(k, l)$ such that for every $n$, every graph $G$ on $n$ vertices containing no cycle of length $3, 4, \dots, 2l$ and no cycle of length $2k+1$, and every vertex $v$ of $G$,
--
--   $$e\big(N_l(v)\big) \le C\,|N_l(v)| \quad\text{and}\quad e\big(N_l(v)\big) \le C\,n,$$
--
--   where $N_l(v)$ is the set of vertices at distance exactly $l$ from $v$ and $e(S)$ is the number of edges with both endpoints in $S$.
--
--   Together with the bound of the copies of $C_{2l+1}$ through $v$ by $e(N_l(v))$, summing over the $n$ vertices gives the $O(n^2)$ upper bound of Theorem 18.
--
--   **Formalization Note** The page's $O(\cdot)$ is pinned to a single constant chosen before $n$, the graph and the vertex, depending only on $k$ and $l$; a constant allowed to depend on the graph would make the claim trivial. The paper's proof (via the Erdős–Gallai path theorem) gives $C = 2(k - l)$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 29, Claim 19

import Mathlib
import Definitions.Def_EvenCycleTuran_OddGirthOdd_Setting

namespace EvenCycleTuran.OddGirthOdd

/-- Claim 19, p. 29: in a graph with no cycle of length 3, …, 2l or 2k+1, the number of edges
inside `N_l(v)` is `O(|N_l(v)|) = O(n)`, with one constant depending only on `k` and `l`. -/
theorem claim_19 (k l : ℕ) (hl : 2 ≤ l) (hkl : l < k) :
    ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      CycleFree (Set.Icc 3 (2 * l) ∪ {2 * k + 1}) G →
      ∀ v : Fin n,
        (edgesInside G (layer G v l) : ℝ) ≤ C * ((layer G v l).ncard : ℝ) ∧
        (edgesInside G (layer G v l) : ℝ) ≤ C * (n : ℝ) := by sorry

end EvenCycleTuran.OddGirthOdd
