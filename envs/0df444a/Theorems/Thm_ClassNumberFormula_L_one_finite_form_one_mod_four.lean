-- Prove2me | Theorems.Thm_ClassNumberFormula_L_one_finite_form_one_mod_four
-- name    : ClassNumberFormula.L_one_finite_form_one_mod_four
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T13:01:12.185675+00:00
-- url     : https://prove2.me/theorems/8481cbdb-a27c-4a7d-80e2-91f049bf37ea
-- title:
--   Finite form of $L(1,\chi)$ for prime conductor $q\equiv1\pmod 4$
-- statement:
--   Let $q$ be a prime with $q\equiv 1\pmod 4$, and let $\chi$ be the Dirichlet character modulo $q$ given by the Legendre symbol, $\chi(m) = \left(\frac{m}{q}\right)$. Then
--   $$L(1,\chi) = -\frac{1}{q^{1/2}}\sum_{m=1}^{q-1}\left(\frac{m}{q}\right)\ln\left(\sin\frac{m\pi}{q}\right).$$
--
--   Combined with the case $d = q$ of Dirichlet's formula, this gives a finite expression for the class number in terms of logarithms of sines.
--
--   **Formalization Note** The source PDF prints the constant $-\frac{1}{2q^{1/2}}$. With the sum over all $m=1,\dots,q-1$ that constant is off by a factor $2$: for $q=5$, $L(1,\chi)=\frac{2}{\sqrt5}\ln\frac{1+\sqrt5}{2}\approx0.4304$, while $-\frac{1}{\sqrt5}\sum_{m=1}^{4}\left(\frac m5\right)\ln\sin\frac{m\pi}{5}\approx0.4304$ and the printed constant gives half of this. The statement here uses $-\frac{1}{q^{1/2}}$. In the source, $\chi = \left(\frac{d}{\cdot}\right)$ with $d = q$, which equals $\left(\frac{m}{q}\right)$ by quadratic reciprocity.
-- source:
--   Wikipedia, "Class number formula" (revision oldid=1366411311), https://en.wikipedia.org/w/index.php?title=Class_number_formula&oldid=1366411311, section "Dirichlet class number formula", last displayed formula, case $q \equiv 1 \pmod 4$ — corrected constant, see Formalization Note

import Mathlib
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace ClassNumberFormula

theorem L_one_finite_form_one_mod_four (q : ℕ) [Fact q.Prime] (hq : q % 4 = 1)
    (χ : DirichletCharacter ℂ q) (hχ : ∀ m : ℕ, χ m = (legendreSym q m : ℂ)) :
    χ.LFunction 1 = ((-(1 / Real.sqrt q) * ∑ m ∈ Finset.Ico 1 q,
      (legendreSym q m : ℝ) * Real.log (Real.sin (m * π / q)) : ℝ) : ℂ) := by sorry

end ClassNumberFormula
