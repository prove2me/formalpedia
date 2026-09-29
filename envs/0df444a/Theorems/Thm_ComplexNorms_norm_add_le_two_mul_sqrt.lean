-- Prove2me | Theorems.Thm_ComplexNorms_norm_add_le_two_mul_sqrt
-- name    : ComplexNorms.norm_add_le_two_mul_sqrt
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:02:35.259077+00:00
-- url     : https://prove2.me/theorems/5666eaa9-3253-4094-b8ec-af9198e29374
-- title:
--   A sum of two numbers bounded by $\sqrt q$ has norm at most $2\sqrt q$
-- statement:
--   **The triangle inequality, in the form used for Frobenius eigenvalues.**
--
--   If $|\alpha| \le \sqrt q$ and $|\beta| \le \sqrt q$, then
--
--   $$|\alpha + \beta| \;\le\; 2\sqrt q .$$
--
--   This is the triangle inequality followed by the two hypotheses, and it is recorded because of
--   where it is applied. For an elliptic curve over $\mathbb{F}_q$ the number of rational points is
--   $\#E(\mathbb{F}_q) = q + 1 - a_q$ with $a_q = \alpha + \beta$, where $\alpha,\beta$ are the
--   eigenvalues of the Frobenius endomorphism. Hasse's theorem is the bound
--
--   $$|a_q| \;\le\; 2\sqrt q,$$
--
--   and it follows from this lemma once the individual eigenvalue bounds $|\alpha|, |\beta| \le \sqrt q$
--   have been established — the analytically substantial step, by an extension-of-scalars or
--   Stepanov-type argument.
--
--   **Formalization note.** No hypothesis $q \ge 0$ is needed: if $q < 0$ then `Real.sqrt q = 0`,
--   the hypotheses force $\alpha = \beta = 0$, and the conclusion holds.
-- source:
--   Classical; the final step of Hasse's theorem, see Silverman, *The Arithmetic of Elliptic Curves*, Ch. V. Lean proof extracted from `Salt/Weil/MultiExtract.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace ComplexNorms

theorem norm_add_le_two_mul_sqrt (α β : ℂ) (q : ℝ) (hα : ‖α‖ ≤ Real.sqrt q)
    (hβ : ‖β‖ ≤ Real.sqrt q) :
    ‖α + β‖ ≤ 2 * Real.sqrt q := by sorry

end ComplexNorms
