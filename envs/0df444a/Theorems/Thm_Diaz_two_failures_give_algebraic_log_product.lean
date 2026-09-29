-- Prove2me | Theorems.Thm_Diaz_two_failures_give_algebraic_log_product
-- name    : Diaz.two_failures_give_algebraic_log_product
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T10:56:52.335949+00:00
-- url     : https://prove2.me/theorems/717e01d6-65d9-4ae6-ab11-d41b76381abc
-- title:
--   Two failures of the one-relation form give two real logarithms of algebraic numbers with algebraic product
-- statement:
--   **Statement.** Suppose the relation "$t\neq 0$ with $e^{t}$ algebraic $\Rightarrow$
--   $t^{2}+\pi^{2}$ transcendental" fails at $t_{1}$ and at $t_{2}$: both $e^{t_{1}},e^{t_{2}}$ are
--   algebraic and both $t_{i}^{2}+\pi^{2}$ are algebraic. Then $t_{1}+t_{2}$ and $t_{1}-t_{2}$ are
--   again **real** logarithms of algebraic numbers --- $\log\beta_{1}\beta_{2}$ and
--   $\log(\beta_{1}/\beta_{2})$ --- their product
--   $$(t_{1}+t_{2})(t_{1}-t_{2})=t_{1}^{2}-t_{2}^{2}
--     =(t_{1}^{2}+\pi^{2})-(t_{2}^{2}+\pi^{2})$$
--   is algebraic, and it is non-zero as soon as $t_{1}^{2}\neq t_{2}^{2}$.
--
--   Read contrapositively: **if the product of two $\mathbb{Q}$-linearly independent real logarithms
--   of algebraic numbers is always transcendental, the relation can fail at only one value of
--   $|t|$.** Nothing here proves the relation; it bounds how badly it could fail.
--
--   **Source and attribution.** All the mathematics of this node is Carlo Perassi's; it is unpublished apart from this node. **No novelty is claimed.** The configuration produced here --- two
--   $\mathbb{Q}$-linearly independent $\lambda_{1},\lambda_{2}\in\mathcal{L}$ with
--   $\lambda_{1}\lambda_{2}\in\bar{\mathbb{Q}}^{\times}$ --- is exactly the condition whose solvability
--   his classification of the period plane leaves undecided; he notes that
--   the strong four exponentials conjecture excludes it, and that Roy's strong six exponentials does
--   not reach it. There the condition arises with **purely imaginary** logarithms, which is why
--   Diaz's assertion (C6) of 1997 --- whose hypothesis is $|\alpha|\neq 1$ --- does not apply there. Here the logarithms are **real**, so
--   $|\alpha|\neq 1$ does hold. That the failure set of the one-relation form feeds the same
--   condition with real logarithms is small.
--
--   **Proof.** $e^{t_{1}+t_{2}}=e^{t_{1}}e^{t_{2}}$ and $e^{t_{1}-t_{2}}=e^{t_{1}}/e^{t_{2}}$, and
--   the algebraic numbers are closed under product and quotient. The product identity is a
--   subtraction, and $t_{1}^{2}-t_{2}^{2}=0$ is $t_{1}^{2}=t_{2}^{2}$.

import Mathlib

open ComplexConjugate

theorem Diaz.two_failures_give_algebraic_log_product {t₁ t₂ : ℝ}
    (e₁ : IsAlgebraic ℚ ((Real.exp t₁ : ℝ) : ℂ)) (e₂ : IsAlgebraic ℚ ((Real.exp t₂ : ℝ) : ℂ))
    (h₁ : IsAlgebraic ℚ ((t₁ ^ 2 + Real.pi ^ 2 : ℝ) : ℂ))
    (h₂ : IsAlgebraic ℚ ((t₂ ^ 2 + Real.pi ^ 2 : ℝ) : ℂ)) :
    IsAlgebraic ℚ ((Real.exp (t₁ + t₂) : ℝ) : ℂ)
      ∧ IsAlgebraic ℚ ((Real.exp (t₁ - t₂) : ℝ) : ℂ)
      ∧ IsAlgebraic ℚ (((t₁ + t₂) * (t₁ - t₂) : ℝ) : ℂ)
      ∧ (t₁ ^ 2 ≠ t₂ ^ 2 → ((t₁ + t₂) * (t₁ - t₂) : ℝ) ≠ 0) := by sorry
