-- Prove2me | Theorems.Thm_ClassNumberFormula_kronecker_is_dirichlet_character
-- name    : ClassNumberFormula.kronecker_is_dirichlet_character
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:54:15.616496+00:00
-- url     : https://prove2.me/theorems/fa5ff86e-46bd-4bb0-a2e0-0f69539c7dd0
-- title:
--   For a fundamental discriminant $d$, $\chi = \left(\frac{d}{\cdot}\right)$ is a Dirichlet character mod $|d|$
-- statement:
--   Let $d$ be a fundamental discriminant. Then there is a Dirichlet character $\chi$ modulo $|d|$ such that
--   $$\chi(n) = \left(\frac{d}{n}\right)\quad\text{for all } n \ge 0,$$
--   where $\left(\frac{d}{n}\right)$ is the Kronecker symbol.
--
--   This is the character whose $L$-function appears in Dirichlet's class number formula. It also shows that the hypotheses used in the Dirichlet formula milestones can be satisfied.
--
--   **Formalization Note** The character is a `DirichletCharacter ℂ |d|`, i.e. a multiplicative character on $\mathbb Z/|d|\mathbb Z$; the statement says it agrees with the Kronecker symbol on every natural number.
-- source:
--   Wikipedia, "Class number formula" (revision oldid=1366411311), https://en.wikipedia.org/w/index.php?title=Class_number_formula&oldid=1366411311, section "Dirichlet class number formula" ("Let $\chi = (d/m)$ be the Kronecker symbol. Then $\chi$ is a Dirichlet character."); H. Davenport, Multiplicative Number Theory, 3rd ed., GTM 74, Springer 2000, Ch. 6 (pp. 43–53)

import Mathlib
import Definitions.Def_ClassNumberFormula_Kronecker
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace ClassNumberFormula

theorem kronecker_is_dirichlet_character (d : ℤ) (hd : IsFundamentalDiscriminant d) :
    ∃ χ : DirichletCharacter ℂ d.natAbs, ∀ n : ℕ, χ n = (kroneckerSymbol d n : ℂ) := by sorry

end ClassNumberFormula
