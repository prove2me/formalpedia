-- Prove2me | Theorems.Thm_AppliedComb_Recurrence_first_order
-- name    : AppliedComb.Recurrence.first_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:14:47.784438+00:00
-- url     : https://prove2.me/theorems/c3608f60-aaf3-4492-928b-418ab2f949e6
-- title:
--   Lemma 9.19 — solutions of (A − r)f = 0 are f(n) = c rⁿ
-- statement:
--   Let $V$ be the space of functions $f : \mathbb{Z} \to \mathbb{R}$ and $A$ the advancement operator, $Af(n) = f(n+1)$. Let $r$ be a nonzero real number and let $f \in V$ satisfy the first-order equation $(A - r) f = 0$, that is, $f(n+1) = r f(n)$ for every integer $n$. If $c = f(0)$, then
--
--   $$f(n) = c\, r^n \qquad \text{for every } n \in \mathbb{Z}.$$
--
--   This is the base case $k = 1$ of the Principal Theorem 9.18: the solutions of a first-order equation form the one-dimensional space spanned by $n \mapsto r^n$.
--
--   **Formalization Note.** $(A - r)$ is `advance - r • 1` in `Module.End ℝ (ℤ → ℝ)`, and $r^n$ for negative $n$ is the integer power (`zpow`), well defined since $r \neq 0$.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 200, Lemma 9.19

import Mathlib
import Definitions.Def_AppliedComb_Recurrence_advance

namespace AppliedComb.Recurrence

/-- Keller–Trotter, Lemma 9.19 (p. 200). Let `r ≠ 0`, and let `f : ℤ → ℝ` be a solution to the
operator equation `(A − r) f = 0`. If `c = f(0)`, then `f(n) = c rⁿ` for every `n ∈ ℤ`
(`rⁿ` is an integer power, `zpow`). -/
theorem first_order (r : ℝ) (hr : r ≠ 0) (f : ℤ → ℝ)
    (hf : (advance - r • (1 : Module.End ℝ (ℤ → ℝ))) f = 0) (c : ℝ) (hc : c = f 0) :
    ∀ n : ℤ, f n = c * r ^ n := by sorry

end AppliedComb.Recurrence
