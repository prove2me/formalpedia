-- Prove2me | Theorems.Thm_ClassNumberFormula_dirichlet_class_number_formula_neg
-- name    : ClassNumberFormula.dirichlet_class_number_formula_neg
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:56:21.915853+00:00
-- url     : https://prove2.me/theorems/bbb540f8-505e-419c-9748-ee8c0b3e3231
-- title:
--   Dirichlet class number formula, $d<0$: $h(d)=\frac{w\sqrt{|d|}}{2\pi}L(1,\chi)$
-- statement:
--   Let $d < 0$ be a fundamental discriminant, let $h(d)$ be the number of proper equivalence classes of positive definite binary quadratic forms of discriminant $d$, let $w$ be $2$, $4$ or $6$ according as $d<-4$, $d=-4$ or $d=-3$, and let $\chi$ be the Dirichlet character modulo $|d|$ given by the Kronecker symbol $\chi(n)=\left(\frac{d}{n}\right)$. Then
--   $$h(d) = \frac{w\sqrt{|d|}}{2\pi}\,L(1,\chi).$$
--
--   This is Dirichlet's class number formula for imaginary quadratic discriminants (Dirichlet, 1839).
--
--   **Formalization Note** $L(1,\chi)$ is the value at $s=1$ of Mathlib's `DirichletCharacter.LFunction`. The character is passed as a hypothesis ($\chi$ agrees with the Kronecker symbol); a separate milestone shows that such a character exists, so the statement is not vacuous.
-- source:
--   Wikipedia, "Class number formula" (revision oldid=1366411311), https://en.wikipedia.org/w/index.php?title=Class_number_formula&oldid=1366411311, section "Dirichlet class number formula", displayed formula for $h(d)$, case $d<0$; H. Davenport, Multiplicative Number Theory, 3rd ed., GTM 74, Springer 2000, Ch. 6 (pp. 43–53)

import Mathlib
import Definitions.Def_ClassNumberFormula_Kronecker
import Definitions.Def_ClassNumberFormula_FormClassNumber
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace ClassNumberFormula

theorem dirichlet_class_number_formula_neg (d : ℤ) (hd : IsFundamentalDiscriminant d)
    (hneg : d < 0) [NeZero d.natAbs] (χ : DirichletCharacter ℂ d.natAbs)
    (hχ : ∀ n : ℕ, χ n = (kroneckerSymbol d n : ℂ)) :
    (formClassNumber d : ℂ) =
      ((formAutomorphCount d * Real.sqrt |(d : ℝ)| / (2 * π) : ℝ) : ℂ) * χ.LFunction 1 := by
  sorry

end ClassNumberFormula
