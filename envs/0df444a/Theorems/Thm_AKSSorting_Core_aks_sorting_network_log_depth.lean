-- Prove2me | Theorems.Thm_AKSSorting_Core_aks_sorting_network_log_depth
-- name    : AKSSorting.Core.aks_sorting_network_log_depth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T10:19:50.34942+00:00
-- url     : https://prove2.me/theorems/d5ec2944-08d9-4af5-94e8-404a7bb3a0c4
-- title:
--   AKS theorem — sorting networks of depth O(log n) and size O(n log n)
-- statement:
--   There is an absolute constant $c>0$ such that for every $n\ge 2$ there is a comparator network $N$ on $n$ registers that sorts every input and satisfies
--   $$ \operatorname{depth}(N)\le c\log_2 n, \qquad \operatorname{size}(N)\le c\,n\log_2 n . $$
--
--   Here a parallel step is a set of comparators on pairwise disjoint pairs of registers, the depth is the number of parallel steps and the size the number of comparators. In the words of the paper: "We give a sorting network with $cn\log n$ comparisons. The algorithm can be performed in $c\log n$ parallel steps as well, where in a parallel step we compare $n/2$ disjoint pairs."
--
--   Before this result the best sorting networks, Batcher's, had depth $O((\log n)^2)$. Depth $O(\log n)$ is optimal up to the constant, since any comparator network that sorts has depth at least $\log_2 n$.
--
--   **Formalization Note** The constant $c$ is quantified before $n$, so it cannot depend on $n$. $\log_2 n$ is `Real.logb 2 n`; the range $n\ge 2$ avoids $\log_2 1=0$ (for $n=1$ the empty network sorts). Sorting is required for every linearly ordered type and every input, not only for permutations, which for comparator networks is equivalent.
-- source:
--   Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983), p. 1, Abstract and Section 1

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork

namespace AKSSorting.Core

/-- Ajtai–Komlós–Szemerédi (1983), main result (Abstract and §1, p. 1): there is an absolute
constant `c` such that for every `n ≥ 2` there is a sorting network on `n` registers with at most
`c log₂ n` parallel steps of disjoint comparators and at most `c n log₂ n` comparators. -/
theorem aks_sorting_network_log_depth :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∃ N : ComparatorNetwork n,
      (N.depth : ℝ) ≤ c * Real.logb 2 n ∧
      (N.size : ℝ) ≤ c * n * Real.logb 2 n ∧
      N.Sorts := by sorry

end AKSSorting.Core
