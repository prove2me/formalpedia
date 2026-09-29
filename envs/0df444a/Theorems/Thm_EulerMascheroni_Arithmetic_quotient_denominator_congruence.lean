-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_quotient_denominator_congruence
-- name    : EulerMascheroni.Arithmetic.quotient_denominator_congruence
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T13:34:57.376056+00:00
-- url     : https://prove2.me/theorems/358f1352-3358-4777-ba22-717cb159eba6
-- title:
--   Clearing a factorial quotient denominator is a factorial congruence
-- statement:
--   Let $a,D\in\mathbb Z$, $n\ge0$, and $S_n=\sum_{k<n}(-1)^k k!$. Then
--
--   $$D\frac{a-S_n}{n!}\in\mathbb Z\quad\Longleftrightarrow\quad n!\mid D(a-S_n).$$
--
--   This translates denominator clearing for the rational-parameter case into an explicit congruence. The integer witness formulation is intentional; the theorem assumes no unproved arithmetic compatibility of real and $p$-adic values.
-- source:
--   Explicit elementary derivation from the factorial quotient coefficients associated to Conjecture 2 in Fischler–Rivoal, Relations between values of arithmetic Gevrey series, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, p. 4. All identities in this submission are unconditional; the arithmetic division conjecture is not assumed.

import Definitions.Def_eulerMascheroni_factorialQuotient

theorem EulerMascheroni.Arithmetic.quotient_denominator_congruence (a D : ℤ) (n : ℕ) :
    (∃ m : ℤ, (D : ℝ) * EulerMascheroni.Arithmetic.quotientCoeff (a : ℝ) n = (m : ℝ)) ↔
      (n.factorial : ℤ) ∣ D * (a - ∑ k ∈ Finset.range n, (-1 : ℤ)^k * (k.factorial : ℤ)) := by sorry
