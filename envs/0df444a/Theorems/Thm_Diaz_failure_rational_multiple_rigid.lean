-- Prove2me | Theorems.Thm_Diaz_failure_rational_multiple_rigid
-- name    : Diaz.failure_rational_multiple_rigid
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T10:56:55.260875+00:00
-- url     : https://prove2.me/theorems/7d5c47fd-2185-4c17-b741-9f268ce4e85f
-- title:
--   A rational multiple of a failure of the one-relation form is a failure only for the multiplier plus or minus one
-- statement:
--   **Statement.** Suppose $t_{1}\neq 0$, $e^{t_{1}}$ is algebraic, and both
--   $t_{1}^{2}+\pi^{2}$ and $t_{2}^{2}+\pi^{2}$ are algebraic, with $t_{2}=r\,t_{1}$ for a rational
--   $r$. Then $r=\pm 1$.
--
--   So the set where the relation "$t\neq 0$, $e^{t}$ algebraic $\Rightarrow$ $t^{2}+\pi^{2}$
--   transcendental" fails is rigid under $\mathbb{Q}^{\times}$: no rational multiple of a failure
--   other than $\pm$ itself is a failure. Combined with
--   `Diaz.two_failures_give_algebraic_log_product`, distinct failure classes $\{b,b^{-1}\}$ are
--   $\mathbb{Q}$-linearly independent and each pair of them produces two real logarithms of algebraic
--   numbers with non-zero algebraic product.
--
--   **Source and attribution.** All the mathematics of this node is Carlo Perassi's. **No novelty is claimed.** The relation whose failures are being constrained is
--   that of Theorem 3.5(ii) of his companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9), a failure being $(\log b)^{2}+\pi^{2}
--   \in\bar{\mathbb{Q}}$ for some real algebraic $b>0$, $b\neq 1$. The rigidity statement itself is
--   small --- it is one application of Hermite--Lindemann --- and it is unpublished apart from this node.
--
--   **Proof.** If $r\neq\pm 1$ then $1-r^{2}\neq 0$, and
--   $(1-r^{2})t_{1}^{2}=(t_{1}^{2}+\pi^{2})-(t_{2}^{2}+\pi^{2})$ is algebraic; dividing by the
--   non-zero rational $1-r^{2}$ makes $t_{1}^{2}$ algebraic, hence $t_{1}$ algebraic. But $t_{1}\neq 0$
--   is algebraic with $e^{t_{1}}$ algebraic, which `DiazModulus.hermite_lindemann_holds` forbids.

import Mathlib

open ComplexConjugate

theorem Diaz.failure_rational_multiple_rigid {t₁ t₂ : ℝ} (ht₁ : t₁ ≠ 0)
    (e₁ : IsAlgebraic ℚ ((Real.exp t₁ : ℝ) : ℂ))
    (h₁ : IsAlgebraic ℚ ((t₁ ^ 2 + Real.pi ^ 2 : ℝ) : ℂ))
    (h₂ : IsAlgebraic ℚ ((t₂ ^ 2 + Real.pi ^ 2 : ℝ) : ℂ))
    (r : ℚ) (hr : t₂ = (r : ℝ) * t₁) : r = 1 ∨ r = -1 := by sorry
