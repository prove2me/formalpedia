-- Prove2me | Theorems.Thm_ClassNumberFormula_dirichlet_class_number_formula_pos
-- name    : ClassNumberFormula.dirichlet_class_number_formula_pos
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:59:58.059201+00:00
-- url     : https://prove2.me/theorems/8823f62e-ebfd-4574-8fa8-5a26f8b77a84
-- title:
--   Dirichlet class number formula, $d>0$: $h(d)=\frac{\sqrt d}{\ln\varepsilon}L(1,\chi)$
-- statement:
--   Let $d > 0$ be a fundamental discriminant, let $h(d)$ be the number of proper ($\mathrm{SL}_2(\mathbb Z)$-) equivalence classes of binary quadratic forms of discriminant $d$, let $\varepsilon = \frac12(t + u\sqrt d)$ where $t>0$, $u>0$ is the solution of $t^2 - du^2 = 4$ with $u$ minimal, and let $\chi$ be the Dirichlet character modulo $d$ given by $\chi(n) = \left(\frac{d}{n}\right)$. Then
--   $$h(d) = \frac{\sqrt d}{\ln \varepsilon}\,L(1,\chi).$$
--
--   This is Dirichlet's class number formula for real quadratic discriminants.
--
--   **Formalization Note** The source PDF prints $\frac{\sqrt d}{2\ln\varepsilon}L(1,\chi)$. With $h(d)$ and $\varepsilon$ defined as in the source, that constant is off by a factor $2$: for $d=5$ one has $h(5)=1$, $\varepsilon=\frac{3+\sqrt5}{2}$ and $L(1,\chi)=\frac{2}{\sqrt5}\ln\frac{1+\sqrt5}{2}$, so $\frac{\sqrt5}{\ln\varepsilon}L(1,\chi)=1$, while the printed formula gives $\frac12$. The statement here follows Davenport, *Multiplicative Number Theory*, Ch. 6, the exposition the source says it follows: $h(d)\ln\varepsilon = \sqrt d\,L(1,\chi)$.
-- source:
--   Wikipedia, "Class number formula" (revision oldid=1366411311), https://en.wikipedia.org/w/index.php?title=Class_number_formula&oldid=1366411311, section "Dirichlet class number formula", displayed formula for $h(d)$, case $d>0$ — corrected constant, following H. Davenport, Multiplicative Number Theory, 3rd ed., GTM 74, Springer 2000, Ch. 6 (pp. 43–53)

import Mathlib
import Definitions.Def_ClassNumberFormula_Kronecker
import Definitions.Def_ClassNumberFormula_FormClassNumber
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace ClassNumberFormula

theorem dirichlet_class_number_formula_pos (d : ℤ) (hd : IsFundamentalDiscriminant d)
    (hpos : 0 < d) [NeZero d.natAbs] (χ : DirichletCharacter ℂ d.natAbs)
    (hχ : ∀ n : ℕ, χ n = (kroneckerSymbol d n : ℂ)) :
    (formClassNumber d : ℂ) =
      ((Real.sqrt d / Real.log (pellEpsilon d) : ℝ) : ℂ) * χ.LFunction 1 := by
  sorry

end ClassNumberFormula
