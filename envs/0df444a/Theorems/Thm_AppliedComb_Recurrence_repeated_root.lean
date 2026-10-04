-- Prove2me | Theorems.Thm_AppliedComb_Recurrence_repeated_root
-- name    : AppliedComb.Recurrence.repeated_root
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:16:37.938998+00:00
-- url     : https://prove2.me/theorems/6c476322-86bf-46e9-9ead-a5ef825673c1
-- title:
--   Lemma 9.22 — the general solution of (A − r)^k f = 0 is (c₁ + c₂n + ⋯ + c_k n^(k−1)) rⁿ
-- statement:
--   Let $V$ be the space of functions $f : \mathbb{Z} \to \mathbb{R}$ and $A$ the advancement operator. Let $k \ge 1$ be an integer and $r$ a nonzero real number, and consider the equation
--
--   $$(A - r)^k f = 0. \qquad (9.5.7)$$
--
--   Then the general solution of (9.5.7) is
--
--   $$f(n) = c_1 r^n + c_2 n r^n + c_3 n^2 r^n + c_4 n^3 r^n + \cdots + c_k n^{k-1} r^n, \qquad (9.5.8)$$
--
--   that is, a function $f \in V$ solves (9.5.7) if and only if there are real constants $c_1, \dots, c_k$ with (9.5.8) for every $n \in \mathbb{Z}$.
--
--   This handles a repeated root of the characteristic polynomial; combined with Theorem 9.21 it gives the general solution of any constant-coefficient linear recurrence whose characteristic polynomial splits over $\mathbb{R}$.
--
--   **Formalization Note.** The book's statement does not repeat $r \neq 0$; it is the standing assumption of Section 9.5.2 (p. 200, "an equation of the form $(A - r)f = 0$ where $r \neq 0$") and is added as a hypothesis. "General solution" is read as an equality of sets, so the Lean statement is an `iff`. The constant `c i` for `i : Fin k` is the book's $c_{i+1}$ and multiplies $n^i r^n$ (with $n^0 = 1$); $n$ is cast to $\mathbb{R}$ and $r^n$ is the integer power.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 201, Lemma 9.22

import Mathlib
import Definitions.Def_AppliedComb_Recurrence_advance

namespace AppliedComb.Recurrence

/-- Keller–Trotter, Lemma 9.22 (p. 201). Let `k ≥ 1` and `r ≠ 0` (the standing assumption of
Section 9.5.2, p. 200: the book's lemma is stated for a root `r` of an equation `(A − r) f = 0`
with `r ≠ 0`). Then the general solution `f : ℤ → ℝ` of `(A − r)^k f = 0` (9.5.7) is
`f(n) = c₁ rⁿ + c₂ n rⁿ + c₃ n² rⁿ + ⋯ + c_k n^(k-1) rⁿ` (9.5.8): a function solves (9.5.7) if and
only if it has this form for some real constants `c₁, …, c_k` (here `c i` for `i : Fin k`
multiplies `n^i rⁿ`, so `c 0` is the book's `c₁`). -/
theorem repeated_root (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr : r ≠ 0) (f : ℤ → ℝ) :
    ((advance - r • (1 : Module.End ℝ (ℤ → ℝ))) ^ k) f = 0 ↔
      ∃ c : Fin k → ℝ, ∀ n : ℤ, f n = ∑ i : Fin k, c i * (n : ℝ) ^ (i : ℕ) * r ^ n := by sorry

end AppliedComb.Recurrence
