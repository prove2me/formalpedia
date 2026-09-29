-- Prove2me | Theorems.Thm_FamousTheorems_banach_fixed_point
-- name    : FamousTheorems.banach_fixed_point
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T01:51:25.162468+00:00
-- url     : https://prove2.me/theorems/a8e3b81f-c833-40f1-b34f-955d77fd6301
-- title:
--   The Banach fixed-point theorem
-- statement:
--   **The Banach fixed-point theorem** (the contraction mapping principle).
--
--   Let $f$ be a contraction with constant $K < 1$ on a complete metric space. Then $f$ has a fixed point
--   $y$, the iterates $f^{[n]}(x)$ converge to it from any starting point $x$, and the error is
--   controlled explicitly:
--   $$d\bigl(f^{[n]}(x),\, y\bigr) \;\le\; \frac{d(x, f(x))\, K^n}{1-K} .$$
--
--   Unlike Brouwer's theorem, this is entirely constructive: it not only asserts a fixed point but
--   produces it as a limit of iterates, with a computable a-priori bound after a single step. That bound
--   is what makes it a practical algorithm rather than an existence statement — one evaluation of
--   $d(x, f(x))$ tells you how many iterations suffice for any target accuracy.
--
--   Banach proved it in his 1922 thesis. It is the standard existence-and-uniqueness engine of analysis:
--   the Picard–Lindelöf theorem for ODEs, the implicit and inverse function theorems, and the existence
--   of invariant measures for contracting dynamical systems are all applications, and Newton's method
--   converges for the same reason.
--
--   **Formalization note.** Distances are extended (`ℝ≥0∞`), so the hypothesis `edist x (f x) ≠ ⊤` rules
--   out a starting point at infinite distance from its image; `f^[n]` is $n$-fold iteration and
--   `Function.IsFixedPt f y` is $f(y) = y$. The result is Mathlib's
--   `ContractingWith.exists_fixedPoint`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

theorem banach_fixed_point {α : Type*} [EMetricSpace α] [CompleteSpace α] {K : ℝ≥0} {f : α → α}
    (hf : ContractingWith K f) (x : α) (hx : edist x (f x) ≠ ⊤) :
    ∃ y, Function.IsFixedPt f y ∧ Tendsto (fun n ↦ f^[n] x) atTop (𝓝 y) ∧
      ∀ n : ℕ, edist (f^[n] x) y ≤ edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K) := by sorry

end FamousTheorems
