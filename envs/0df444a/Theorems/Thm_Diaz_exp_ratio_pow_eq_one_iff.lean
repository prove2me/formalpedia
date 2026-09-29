-- Prove2me | Theorems.Thm_Diaz_exp_ratio_pow_eq_one_iff
-- name    : Diaz.exp_ratio_pow_eq_one_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T10:56:52.892524+00:00
-- url     : https://prove2.me/theorems/5770449d-2fad-43ac-bf84-f50a6a4693b7
-- title:
--   The unimodular part of an exponential has order dividing m exactly when m·Im v lies in πℤ
-- statement:
--   **Statement.** For $v\in\mathbb{C}$ and $m\in\mathbb{N}$,
--   $$\left(\frac{e^{v}}{\overline{e^{v}}}\right)^{m}=1
--     \qquad\Longleftrightarrow\qquad m\,\Im v\in\pi\mathbb{Z}.$$
--
--   Writing $\alpha=e^{v}$, the left-hand side says that $\alpha/\bar\alpha$ --- equivalently
--   $(\alpha/|\alpha|)^{2}$ --- is a root of unity of order dividing $m$.
--
--   **Source and attribution.** All the mathematics of this node is Carlo Perassi's. **No novelty is claimed.** The condition is clause (i) of his
--   torsion dichotomy, "$\alpha/|\alpha|$ is a root of unity", in the
--   quantitative form in which it appears as the hypothesis $\xi^{m}=1$ of his effective lower
--   bound in the torsion branch --- published on this board as
--   `Diaz.order_quantisation`. The equivalence with $m\,\Im v\in\pi\mathbb{Z}$ is an elementary
--   computation, which he states in passing rather than as a separate result; it is unpublished
--   apart from this node.
--
--   **Why it is on the board.** `Diaz.order_quantisation` and `Diaz.real_quantisation` take the power
--   condition as a hypothesis. Checking it at a given point otherwise means computing with
--   `Complex.exp` and `conj`; this node turns it once and for all into a linear condition on
--   $\Im v$, which is what makes the quantisation family usable at an arbitrary point of a
--   candidate's rational orbit (see `Diaz.quantisation_orbit_iff_re_ne_zero`).
--
--   **Proof.** $e^{v}/\overline{e^{v}}=e^{v-\bar v}$ and $v-\bar v=2i\,\Im v$, so the $m$-th power
--   is $e^{2mi\,\Im v}$; `Complex.exp_eq_one_iff` turns that into
--   $2mi\,\Im v\in 2\pi i\mathbb{Z}$, and comparing imaginary parts in both directions finishes
--   it.

import Mathlib

open ComplexConjugate

theorem Diaz.exp_ratio_pow_eq_one_iff (v : ℂ) (m : ℕ) :
    (Complex.exp v / conj (Complex.exp v)) ^ m = 1
      ↔ ∃ n : ℤ, (m : ℝ) * v.im = (n : ℝ) * Real.pi := by sorry
