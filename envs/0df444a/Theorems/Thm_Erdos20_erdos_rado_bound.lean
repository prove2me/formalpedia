-- Prove2me | Theorems.Thm_Erdos20_erdos_rado_bound
-- name    : Erdos20.erdos_rado_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:27:20.454152+00:00
-- url     : https://prove2.me/theorems/584b1456-6903-4b5a-8226-8001260a0079
-- title:
--   Erdős–Rado upper bound $f(n,k) \le (k-1)^n n! + 1$
-- statement:
--   Let $f(n,k)$ be the sunflower threshold. For all integers $n \ge 1$ and $k \ge 2$,
--
--   $$f(n,k) \le (k-1)^n\, n! + 1,$$
--
--   that is, every family of more than $(k-1)^n n!$ sets of size $n$ contains a $k$-sunflower. This is the original sunflower lemma of Erdős and Rado (1960) and shows that $f(n,k)$ is finite.
-- source:
--   Formal Conjectures, `FormalConjectures/ErdosProblems/20.lean` (Erdős Problem 20), https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/20.lean ; https://www.erdosproblems.com/20 (theorem `erdos_20.variants.erdos_rado_bound`) ; P. Erdős and R. Rado, Intersection theorems for systems of sets, J. London Math. Soc. 35 (1960), 85–90, https://doi.org/10.1112/jlms/s1-35.1.85

import Definitions.Def_Erdos20_defs
import Mathlib

namespace Erdos20
theorem erdos_rado_bound :
    ∀ n k, n > 0 → 2 ≤ k → f n k ≤ (k - 1) ^ n * n.factorial + 1 := by sorry
end Erdos20
