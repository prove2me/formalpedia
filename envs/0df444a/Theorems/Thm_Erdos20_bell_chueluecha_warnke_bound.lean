-- Prove2me | Theorems.Thm_Erdos20_bell_chueluecha_warnke_bound
-- name    : Erdos20.bell_chueluecha_warnke_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T17:40:38.760153+00:00
-- url     : https://prove2.me/theorems/de7f34a4-d9e9-4a94-bbec-05709d403836
-- title:
--   Bell–Chueluecha–Warnke bound $f(n,k) \le (Ck\log n)^n$
-- statement:
--   Let $f(n,k)$ be the sunflower threshold. There is a constant $C \ge 4$ such that for all integers $n \ge 2$ and $k \ge 2$,
--
--   $$f(n,k) \le \bigl(C\, k \log n\bigr)^n.$$
--
--   This is Theorem 1 of Bell, Chueluecha and Warnke (2021), written there as $\mathrm{Sun}(p,k) \le (Cp\log k)^k$ with $p$ petals and set size $k$; it is the best known general upper bound.
--
--   **Formalization Note** $\log$ is the natural logarithm. Their $\mathrm{Sun}(p,k)$ is the least $s$ such that every family of at least $s$ distinct $k$-element sets has a $p$-sunflower, which is exactly $f(k,p)$ here, so no $+1$ appears.
-- source:
--   T. Bell, S. Chueluecha, L. Warnke, Note on sunflowers, Discrete Mathematics 344 (2021), arXiv:2009.09327, Theorem 1 (p. 1)

import Definitions.Def_Erdos20_defs
import Mathlib

namespace Erdos20
theorem bell_chueluecha_warnke_bound :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ n k : ℕ, 2 ≤ n → 2 ≤ k →
      (f n k : ℝ) ≤ (C * k * Real.log n) ^ n := by sorry
end Erdos20
