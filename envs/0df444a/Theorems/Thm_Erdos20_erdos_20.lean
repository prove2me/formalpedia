-- Prove2me | Theorems.Thm_Erdos20_erdos_20
-- name    : Erdos20.erdos_20
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:42:01.575841+00:00
-- url     : https://prove2.me/theorems/b54fabc4-8f60-4a35-8829-bd039b83d8fa
-- title:
--   Erdős Problem 20: the sunflower conjecture
-- statement:
--   Let $f(n,k)$ be the least $m$ such that every family of $n$-element sets with at least $m$ members contains a $k$-sunflower (a subfamily of $k$ sets with all pairwise intersections equal). Then there are constants $c_k \in \mathbb N$, one for each $k$, such that
--
--   $$f(n,k) < c_k^{\,n} \qquad \text{for all } n \ge 1 \text{ and all } k \in \mathbb N.$$
--
--   This is the sunflower conjecture of Erdős and Rado: for each fixed number of petals, the threshold grows only exponentially in the set size.
--
--   **Formalization Note** The source asks the yes/no question "is it true that …?"; this item states the affirmative claim. A disproof establishes the negative answer.
-- source:
--   Formal Conjectures, `FormalConjectures/ErdosProblems/20.lean` (Erdős Problem 20), https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/20.lean ; https://www.erdosproblems.com/20 (theorem `erdos_20`)

import Definitions.Def_Erdos20_defs
import Mathlib

namespace Erdos20
theorem erdos_20 : ∃ (c : ℕ → ℕ), ∀ n k, n > 0 → f n k < (c k) ^ n := by sorry
end Erdos20
