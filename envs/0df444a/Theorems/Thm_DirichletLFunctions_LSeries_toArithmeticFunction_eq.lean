-- Prove2me | Theorems.Thm_DirichletLFunctions_LSeries_toArithmeticFunction_eq
-- name    : DirichletLFunctions.LSeries_toArithmeticFunction_eq
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:57:49.41055+00:00
-- url     : https://prove2.me/theorems/cfdad958-c6ab-46ce-8be2-501280345837
-- title:
--   The $L$-series of a character agrees with its $L$-function on $\Re s>1$
-- statement:
--   **On the half-plane of absolute convergence, the $L$-function is given by its series.**
--
--   For a Dirichlet character $\chi$ modulo $N$ and $\Re s > 1$,
--
--   $$\sum_{n \ge 1} \frac{\chi(n)}{n^{s}} \;=\; L(s,\chi).$$
--
--   The right-hand side, `DirichletCharacter.LFunction`, is defined by **analytic continuation** to
--   all of $\mathbb{C}$ (with a pole at $s=1$ only for the principal character), so it is not by
--   construction a Dirichlet series. The identity says that on $\Re s > 1$, where the series
--   converges absolutely because $|\chi(n)| \le 1$ and $\sum n^{-\Re s} < \infty$, the continuation
--   agrees with the naive sum.
--
--   This is the bridge every argument crosses. Euler products, convolution identities and
--   coefficient manipulations are all proved for the *series*, valid only on $\Re s > 1$; results
--   about zeros and growth concern the *continuation*, on the whole plane. Without this lemma the
--   two objects could not be identified even where both are defined.
--
--   **Formalization note.** `toArithmeticFunction (χ ·)` coerces the character into
--   `ArithmeticFunction ℂ` (setting the value at $0$ to $0$), and `LSeries` is the formal Dirichlet
--   series; the hypothesis $\Re s > 1$ is exactly absolute convergence.
-- source:
--   Classical; see Apostol, *Introduction to Analytic Number Theory*, §12.5. Lean proof extracted from `Salt/SW/FourFold.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace DirichletLFunctions

open ArithmeticFunction DirichletCharacter in
theorem LSeries_toArithmeticFunction_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (toArithmeticFunction (χ ·)) s = LFunction χ s := by sorry

end DirichletLFunctions
