-- Prove2me | Theorems.Thm_ComplexNorms_norm_eq_sqrt_of_pair_of_le
-- name    : ComplexNorms.norm_eq_sqrt_of_pair_of_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T16:26:09.62873+00:00
-- url     : https://prove2.me/theorems/dedf6a52-0568-407e-96f4-8a4b9fb9deb8
-- title:
--   A rigidity lemma: two factors bounded by $\sqrt q$ with product $q$ are both $\sqrt q$
-- statement:
--   **Equality is forced when a product attains the extreme allowed by individual bounds.**
--
--   Let $\alpha, \beta \in \mathbb{C}$ and $q \ge 0$ satisfy
--
--   $$|\alpha\beta| = q, \qquad |\alpha| \le \sqrt q, \qquad |\beta| \le \sqrt q .$$
--
--   Then necessarily $|\alpha| = |\beta| = \sqrt q$.
--
--   The argument is a rigidity statement: from $|\alpha||\beta| = q = \sqrt q \cdot \sqrt q$ and
--   both factors bounded above by $\sqrt q$, neither can be strictly smaller, since a strict
--   inequality in one factor would force the product below $q$.
--
--   Despite its simplicity this is the standard final step in deducing the **Riemann hypothesis for
--   curves over finite fields** in the elementary treatments: the Frobenius eigenvalues
--   $\alpha, \beta$ of an elliptic curve over $\mathbb{F}_q$ satisfy $\alpha\beta = q$ by the
--   Weil pairing, and one proves the *one-sided* bounds $|\alpha|, |\beta| \le \sqrt q$ by an
--   extension-of-scalars or Stepanov-type argument. This lemma then upgrades those inequalities to
--   the exact statement $|\alpha| = |\beta| = \sqrt q$, i.e. the eigenvalues lie on the critical
--   circle.
--
--   **Formalization note.** Norms are the complex absolute value; $q \ge 0$ makes $\sqrt q$
--   meaningful and `Real.sqrt` is the non-negative square root.
-- source:
--   Classical; the extraction step in Hasse's theorem and the Weil conjectures for curves, cf. Silverman, *The Arithmetic of Elliptic Curves*, Ch. V. Lean proof extracted from `Salt/Weil/MultiExtract.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace ComplexNorms

theorem norm_eq_sqrt_of_pair_of_le (α β : ℂ) (q : ℝ) (hq : 0 ≤ q) (hprod : ‖α * β‖ = q)
    (hα : ‖α‖ ≤ Real.sqrt q) (hβ : ‖β‖ ≤ Real.sqrt q) :
    ‖α‖ = Real.sqrt q ∧ ‖β‖ = Real.sqrt q := by sorry

end ComplexNorms
