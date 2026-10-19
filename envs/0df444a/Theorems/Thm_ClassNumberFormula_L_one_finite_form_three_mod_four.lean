-- Prove2me | Theorems.Thm_ClassNumberFormula_L_one_finite_form_three_mod_four
-- name    : ClassNumberFormula.L_one_finite_form_three_mod_four
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T13:00:59.312541+00:00
-- url     : https://prove2.me/theorems/6203d632-21a3-4e9d-9041-714f858da8ec
-- title:
--   Finite form of $L(1,\chi)$ for prime conductor $q\equiv3\pmod 4$
-- statement:
--   Let $q$ be a prime with $q\equiv 3\pmod 4$, and let $\chi$ be the Dirichlet character modulo $q$ given by the Legendre symbol, $\chi(m) = \left(\frac{m}{q}\right)$. Then
--   $$L(1,\chi) = -\frac{\pi}{q^{3/2}}\sum_{m=1}^{q-1} m\left(\frac{m}{q}\right).$$
--
--   Combined with the case $d=-q$ of Dirichlet's formula, this gives a finite expression for the class number.
--
--   **Formalization Note** In the source, $\chi = \left(\frac{d}{\cdot}\right)$ is primitive with prime conductor $q$, so $d = -q$, and by quadratic reciprocity $\chi(m) = \left(\frac{m}{q}\right)$; the statement uses this explicit description. $L(1,\chi)$ is Mathlib's `DirichletCharacter.LFunction` at $s=1$.
-- source:
--   Wikipedia, "Class number formula" (revision oldid=1366411311), https://en.wikipedia.org/w/index.php?title=Class_number_formula&oldid=1366411311, section "Dirichlet class number formula", last displayed formula, case $q \equiv 3 \pmod 4$

import Mathlib
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace ClassNumberFormula

theorem L_one_finite_form_three_mod_four (q : ℕ) [Fact q.Prime] (hq : q % 4 = 3)
    (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ)) :
    χ.LFunction 1 = ((-(π / (q : ℝ) ^ ((3 : ℝ) / 2)) *
      ∑ m ∈ Finset.Ico 1 q, (m : ℝ) * (legendreSym q m : ℝ) : ℝ) : ℂ) := by sorry

end ClassNumberFormula
