-- Prove2me | Theorems.Thm_DirichletCharacters_fourfold_vonMangoldt_nonneg
-- name    : DirichletCharacters.fourfold_vonMangoldt_nonneg
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T16:13:32.388286+00:00
-- url     : https://prove2.me/theorems/6d7a28c1-7176-4e03-82e5-efb33537eaef
-- title:
--   Landau's fourfold positivity for two quadratic characters
-- statement:
--   **A positivity identity for two quadratic characters.**
--
--   Let $\chi_1, \chi_2$ be quadratic (real) Dirichlet characters modulo $N$, that is
--   $\chi_i^2 = \chi_0$. Then for every $n$,
--
--   $$\Lambda(n)\Bigl(1 + \Re\chi_1(n) + \Re\chi_2(n) + \Re(\chi_1\chi_2)(n)\Bigr) \;\ge\; 0,$$
--
--   where $\Lambda$ is the von Mangoldt function.
--
--   The point is the elementary factorisation available for **real** characters: since each
--   $\chi_i(n) \in \{0, \pm1\}$ on the integers coprime to $N$, one has
--
--   $$1 + \chi_1(n) + \chi_2(n) + \chi_1(n)\chi_2(n) = \bigl(1 + \chi_1(n)\bigr)\bigl(1 + \chi_2(n)\bigr) \;\ge\; 0,$$
--
--   a product of two non-negative factors, while $\Lambda(n) \ge 0$ always. On $n$ sharing a factor
--   with $N$ every character vanishes and the bracket is $1 > 0$.
--
--   This is the four-character analogue of the classical $3 + 4\cos\theta + \cos 2\theta \ge 0$
--   trick. Summed against $n^{-s}$ it says that the Dirichlet series
--   $\zeta(s)L(s,\chi_1)L(s,\chi_2)L(s,\chi_1\chi_2)$ has non-negative logarithmic coefficients,
--   which is exactly the input to Landau's argument bounding exceptional real zeros: if two distinct
--   quadratic characters both had zeros very close to $s = 1$, the product would be forced to be
--   small where positivity says it cannot be.
--
--   **Formalization note.** `vonMangoldt` is Mathlib's $\Lambda$, and the real parts are taken
--   because characters are $\mathbb{C}$-valued even when quadratic.
-- source:
--   Classical; Landau's argument for exceptional zeros, see Davenport, *Multiplicative Number Theory*, §14, and Iwaniec & Kowalski, *Analytic Number Theory*, §5.9. Lean proof extracted from `Salt/SW/FourFold.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace DirichletCharacters

open ArithmeticFunction in
theorem fourfold_vonMangoldt_nonneg {N : ℕ} {χ₁ χ₂ : DirichletCharacter ℂ N}
    (hχ₁ : χ₁ ^ 2 = 1) (hχ₂ : χ₂ ^ 2 = 1) (n : ℕ) :
    0 ≤ vonMangoldt n * (1 + (χ₁ n).re + (χ₂ n).re + ((χ₁ * χ₂) n).re) := by sorry

end DirichletCharacters
