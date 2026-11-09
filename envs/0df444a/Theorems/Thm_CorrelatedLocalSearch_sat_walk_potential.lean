-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_sat_walk_potential
-- name    : CorrelatedLocalSearch.sat_walk_potential
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:40:14.9443+00:00
-- url     : https://prove2.me/theorems/8e419190-caf6-4d04-8391-9c90492e4282
-- title:
--   Proof of Theorem 4.1 — the Hamming distance to a strong witness is an integer potential
-- statement:
--   Let $k/2<r<k$, let $\Phi$ be a $k$-CNF on $n$ variables with strong witness $x^*$, and write $d(x)=d_H(x,x^*)$ for the Hamming distance.
--
--   1. If a clause $C$ of $\Phi$ is violated by $x$, then at least $r$ of the $k$ literal positions $i$ of $C$ have the property that flipping the variable of the $i$-th literal decreases $d$ by one.
--   2. Flipping any variable changes $d$ by exactly one: $d(x')=d(x)+1$ or $d(x')=d(x)-1$.
--   3. Every $x$ with $d(x)=0$ satisfies $\Phi$; equivalently, every live (unsatisfying) assignment has positive potential.
--
--   Hence the promise-SAT walk, with potential $d(x_t)$, satisfies the hypotheses of Lemma C.1 with $h=d_H(x_0,x^*)$ whenever $h\ge1$.
--
--   **Formalization Note** Flips are counted by literal position with `Set.ncard`; $d_H$ is Mathlib's `hammingDist`.
--
--   Differences from the source:
--   - encoding: integers k/2 < r < k → natural numbers k, r with k < 2r and r < k; reason: same instances
--   - generalization: all flips of a violated clause other than the r decreasing ones increase d by one → every flip of every variable changes d by exactly one, together with clause 1; reason: clause 1 and the ±1 property imply the paper's statement; the ±1 property holds for any flip
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Theorem 4.1, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Clause
import Definitions.Def_CorrelatedLocalSearch_walkTau

set_option autoImplicit false

namespace CorrelatedLocalSearch

/-- The SAT walk has the potential of Lemma C.1 (Xu, *Local Search with Correlated
Randomness*, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Theorem 4.1, p.23): let
`x∗` be a strong witness of the `k`-CNF `Φ` and `d(x) = d_H(x, x∗)`.
1. If a clause `C` of `Φ` is violated by `x`, at least `r` of the `k` flips of its literals'
   variables decrease `d` by one;
2. every flip of a variable changes `d` by exactly one;
3. an assignment at distance `0` from `x∗` satisfies `Φ` ("every live assignment has positive
   potential").

**Formalization Note** Flips are counted by literal position `i : Fin k` (`Set.ncard`); `d_H` is
Mathlib's `hammingDist`. -/
theorem sat_walk_potential (k r n : ℕ) (hk : k < 2 * r) (hr : r < k)
    (Φ : List (Clause k n)) (xs : Fin n → Bool) (hxs : IsStrongWitness r Φ xs) :
    (∀ C ∈ Φ, ∀ x : Fin n → Bool, C.Violated x →
        r ≤ Set.ncard {i : Fin k |
          hammingDist (flipVar x (C.lit i).1) xs + 1 = hammingDist x xs}) ∧
      (∀ (x : Fin n → Bool) (v : Fin n),
        hammingDist (flipVar x v) xs = hammingDist x xs + 1 ∨
          hammingDist (flipVar x v) xs + 1 = hammingDist x xs) ∧
      (∀ x : Fin n → Bool, hammingDist x xs = 0 → Satisfies Φ x) := by sorry

end CorrelatedLocalSearch
