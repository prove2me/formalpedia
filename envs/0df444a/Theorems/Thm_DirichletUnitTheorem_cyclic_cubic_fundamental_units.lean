-- Prove2me | Theorems.Thm_DirichletUnitTheorem_cyclic_cubic_fundamental_units
-- name    : DirichletUnitTheorem.cyclic_cubic_fundamental_units
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:35:38.294068+00:00
-- url     : https://prove2.me/theorems/cf29541a-115a-4e36-8781-5b3b58a4c167
-- title:
--   Fundamental units of the cyclic cubic field $\mathbb Q(\alpha)$, $\alpha^3+\alpha^2-2\alpha-1=0$
-- statement:
--   Let $K$ be a number field with $[K:\mathbb Q]=3$ containing an element $\alpha$ with $\alpha^3+\alpha^2-2\alpha-1=0$ (so $K=\mathbb Q(\alpha)$ is the cyclic cubic field of discriminant $49$). Put $\varepsilon_1=\alpha^2+\alpha-1$ and $\varepsilon_2=2-\alpha^2$. Then $\{\varepsilon_1,\varepsilon_2\}$ is a basis of the unit group of $K$ modulo roots of unity:
--
--   1. $\varepsilon_1,\varepsilon_2\neq0$;
--   2. every unit $u$ of $\mathcal O_K$ can be written as $u=\zeta\,\varepsilon_1^{a}\varepsilon_2^{b}$ with $\zeta$ a root of unity and $a,b\in\mathbb Z$;
--   3. if $\varepsilon_1^{a}\varepsilon_2^{b}$ is a root of unity, then $a=b=0$.
--
--   **Formalization Note** Powers with negative integer exponents are taken in the field $K$.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), section "The regulator", Examples, third bullet (cyclic cubic field; Cohen 1993, Table B.4).

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem cyclic_cubic_fundamental_units (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 3) (α : K) (hα : α ^ 3 + α ^ 2 - 2 * α - 1 = 0) :
    (α ^ 2 + α - 1) ≠ 0 ∧ (2 - α ^ 2) ≠ 0 ∧
    (∀ u : (𝓞 K)ˣ, ∃ ζ : (𝓞 K)ˣ, IsOfFinOrder ζ ∧ ∃ a b : ℤ,
        ((u : 𝓞 K) : K) = ((ζ : 𝓞 K) : K) * (α ^ 2 + α - 1) ^ a * (2 - α ^ 2) ^ b) ∧
    (∀ a b : ℤ, (∃ n : ℕ, 0 < n ∧ ((α ^ 2 + α - 1) ^ a * (2 - α ^ 2) ^ b) ^ n = 1) →
        a = 0 ∧ b = 0) := by sorry

end DirichletUnitTheorem
