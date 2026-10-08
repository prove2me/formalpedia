-- Prove2me | Theorems.Thm_BHTOpinion_Discrete_eq2_3_partial_sums_monotone
-- name    : BHTOpinion.Discrete.eq2_3_partial_sums_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:54.392019+00:00
-- url     : https://prove2.me/theorems/4fd16ac0-2871-43e1-ad69-3991b0e735ce
-- title:
--   Eq. (2.3) — for a sorted proper solution, d/dt Σ_{i≤k} x_i = Σ_{i≤k} Σ_{j>k, |x_i−x_j|<1} (x_j − x_i) ≥ 0 except countably many t; partial sums nondecreasing
-- statement:
--   Let $x$ be a proper solution of (2.1) whose initial condition is sorted, $x_1(0)\le x_2(0)\le\dots\le x_n(0)$. Then for every $k$ the sum of the $k$ lowest opinions
--
--   $$t\ \longmapsto\ \sum_{i=1}^{k}x_i(t)$$
--
--   is differentiable for all $t$ except possibly countably many, with
--
--   $$\frac{d}{dt}\sum_{i=1}^k x_i(t)=\sum_{i=1}^k\ \sum_{j>k:\,|x_i(t)-x_j(t)|<1}\bigl(x_j(t)-x_i(t)\bigr)\ \ge\ 0,\tag{2.3}$$
--
--   the right-hand side being nonnegative because the order of the agents is preserved; and consequently it is nondecreasing on $[0,\infty)$. The monotonicity is what the convergence argument of Theorem 2 uses: bounded monotone partial sums converge.
--
--   **Formalization Note** Agents are `Fin n` (indices $0,\dots,n-1$); the sum over $i\le k$ in the paper's $1$-based labels is the sum over indices $i<k$, the inner sum over $j>k$ is the sum over indices $j\ge k$, and $k$ ranges over all natural numbers ($k=0$ gives the empty sum, $k\ge n$ the total sum with an empty inner sum). "For all $t$, except possibly for countably many" is an explicit countable set $S$ outside of which, at every $t>0$, the partial sum has the stated derivative (`HasDerivAt`) and that derivative is nonnegative; $t>0$ because the two-sided derivative at $0$ would see values at negative times. Sortedness is a hypothesis of this statement only, as in the paper, where it is the convention "the components of proper initial conditions are sorted".
-- source:
--   Blondel, Hendrickx, Tsitsiklis, SIAM J. Control Optim. 48 (2010), proof of Theorem 2, Eq. (2.3), p. 5219

import Mathlib
import Definitions.Def_BHTOpinion_Discrete_Model

open Filter Topology

namespace BHTOpinion.Discrete

theorem eq2_3_partial_sums_monotone {n : ℕ} (x : ℝ → Fin n → ℝ) (hx : IsProperSolution x)
    (hsorted : Monotone (x 0)) (k : ℕ) :
    (∃ S : Set ℝ, S.Countable ∧ ∀ t : ℝ, 0 < t → t ∉ S →
      HasDerivAt (fun s => ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), x s i)
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k),
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => k ≤ (j : ℕ) ∧ |x t i - x t j| < 1),
            (x t j - x t i)) t ∧
      0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k),
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => k ≤ (j : ℕ) ∧ |x t i - x t j| < 1),
            (x t j - x t i)) ∧
    MonotoneOn (fun t => ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), x t i)
      (Set.Ici 0) := by sorry

end BHTOpinion.Discrete
