-- Prove2me | Theorems.Thm_Devaney_exists_orbit_along_covering_chain
-- name    : Devaney.exists_orbit_along_covering_chain
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:10:08.48095+00:00
-- url     : https://prove2.me/theorems/21b9022e-50c4-4246-b59a-0fca9ce012dc
-- title:
--   Second covering observation — orbits following a chain of covering intervals
-- statement:
--   Let $f$ be continuous and let $A_0, A_1, \dots, A_n$ be closed intervals with $f(A_i) \supseteq A_{i+1}$ for $i < n$. Then there is a point $x \in A_0$ whose orbit follows the chain:
--
--   $$f^{i}(x) \in A_i \qquad (0 \le i \le n).$$
--
--   This is the second observation of §1.10 (Exercise 1 of the section), obtained by pulling back a nested sequence of subintervals.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.10, p. 61, second observation; Exercise 1, p. 68

import Mathlib
import Definitions.Def_Devaney_sarkovskii

namespace Devaney
theorem exists_orbit_along_covering_chain (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ)
    (a b : ℕ → ℝ) (hab : ∀ i ≤ n, a i ≤ b i)
    (hcov : ∀ i < n, Covers f (Set.Icc (a i) (b i)) (Set.Icc (a (i + 1)) (b (i + 1)))) :
    ∃ x ∈ Set.Icc (a 0) (b 0), ∀ i ≤ n, f^[i] x ∈ Set.Icc (a i) (b i) := by sorry
end Devaney
