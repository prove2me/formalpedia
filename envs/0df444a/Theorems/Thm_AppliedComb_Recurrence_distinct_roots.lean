-- Prove2me | Theorems.Thm_AppliedComb_Recurrence_distinct_roots
-- name    : AppliedComb.Recurrence.distinct_roots
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:16:02.879823+00:00
-- url     : https://prove2.me/theorems/49b3ef04-94fd-4481-9d76-a30be214ffcf
-- title:
--   Theorem 9.21 — distinct nonzero roots: every solution is c₁r₁ⁿ + ⋯ + c_k r_kⁿ
-- statement:
--   Let $V$ be the space of functions $f : \mathbb{Z} \to \mathbb{R}$ and $A$ the advancement operator. Let $r_1, r_2, \dots, r_k$ be distinct nonzero real constants and consider the equation
--
--   $$p(A) f = (A - r_1)(A - r_2)\cdots(A - r_k) f = 0. \qquad (9.5.4)$$
--
--   Then every solution $f$ of (9.5.4) has the form
--
--   $$f(n) = c_1 r_1^n + c_2 r_2^n + c_3 r_3^n + \cdots + c_k r_k^n \qquad (n \in \mathbb{Z})$$
--
--   for some real constants $c_1, \dots, c_k$.
--
--   This is the general solution of a constant-coefficient linear recurrence whose characteristic polynomial has distinct nonzero real roots, and it is the distinct-roots case of the Principal Theorem 9.18.
--
--   **Formalization Note.** The roots are `r : Fin k → ℝ`, distinct (`Function.Injective r`) and nonzero. The operator is the product, in the book's left-to-right order, of the factors `advance - r i • 1` (`List.prod` of `List.ofFn`, as `Module.End` is not a commutative monoid in Lean). $r_i^n$ is the integer power (`zpow`). Only the inclusion stated on the page is asserted: every solution has this form.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 200, Theorem 9.21

import Mathlib
import Definitions.Def_AppliedComb_Recurrence_advance

namespace AppliedComb.Recurrence

/-- Keller–Trotter, Theorem 9.21 (p. 200). Consider the advancement operator equation
`p(A) f = (A − r₁)(A − r₂) ⋯ (A − r_k) f = 0` (9.5.4) with `r₁, …, r_k` distinct non-zero real
constants (indexed here by `Fin k`; the product is taken in the book's left-to-right order).
Then every solution `f : ℤ → ℝ` of (9.5.4) has the form
`f(n) = c₁ r₁ⁿ + c₂ r₂ⁿ + ⋯ + c_k r_kⁿ` for all `n ∈ ℤ`, for some real constants `c₁, …, c_k`. -/
theorem distinct_roots (k : ℕ) (r : Fin k → ℝ) (hr : Function.Injective r)
    (hr0 : ∀ i, r i ≠ 0) (f : ℤ → ℝ)
    (hf : (List.ofFn fun i : Fin k => advance - r i • (1 : Module.End ℝ (ℤ → ℝ))).prod f = 0) :
    ∃ c : Fin k → ℝ, ∀ n : ℤ, f n = ∑ i : Fin k, c i * r i ^ n := by sorry

end AppliedComb.Recurrence
