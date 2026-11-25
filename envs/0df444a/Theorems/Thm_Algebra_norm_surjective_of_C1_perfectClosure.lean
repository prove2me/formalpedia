-- Prove2me | Theorems.Thm_Algebra_norm_surjective_of_C1_perfectClosure
-- name    : Algebra.norm_surjective_of_C1_perfectClosure
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T07:50:43.278271+00:00
-- url     : https://prove2.me/theorems/ce922dc9-0d07-5bbf-b0e1-87506c5b3388
-- title:
--   Norms are surjective when the perfect closure is $C_1$: $N_{L/F}(L) = F$ for $L/F$ finite separable of degree prime to the characteristic
-- statement:
--   Call a field $K$ **$C_1$** if every polynomial $f \in K[x_1, \dots, x_n]$ (for any $n$) whose total degree is smaller than the number of variables, $\deg f < n$, and whose constant term is $0$ has a nontrivial zero:
--
--   $$\exists\, x \in K^n,\ x \ne 0,\ f(x) = 0.$$
--
--   Let $F$ be a field of exponential characteristic $q$ (so $q = 1$ if $\operatorname{char} F = 0$ and $q = p$ if $\operatorname{char} F = p > 0$), let $L/F$ be a finite separable extension whose degree $[L : F]$ is coprime to $q$, let $\overline{L}$ be an algebraic closure of $L$, and let $F^{\mathrm{perf}} \subseteq \overline{L}$ be the perfect closure of $F$ in $\overline{L}$ (the elements $x$ with $x^{q^n} \in F$ for some $n \ge 0$). If $F^{\mathrm{perf}}$ is $C_1$, then the norm map
--
--   $$N_{L/F} : L \to F$$
--
--   is surjective.
--
--   Role: for a $C_1$ field $K$ the norm of every finite extension of $K$ is surjective (Lang; the Proved theorem `RatFunc.tsen_and_lang_C1`). This statement transfers the conclusion to an imperfect field $F$ that is not known to be $C_1$ itself, when only its perfect closure is $C_1$ and the extension is separable of degree prime to $q$. A typical use is a field $F$ whose perfect closure is an algebraic extension of $\bar k(t)$ with $\bar k$ algebraically closed, for instance the function field of a curve over a separably closed imperfect field $k$: Tsen's theorem applies to $F^{\mathrm{perf}}$ but not directly to $F$, and the statement still gives surjective norms for all finite separable extensions of $F$ of degree prime to $p$ (the input for the prime-to-$p$ part of the Brauer group of $F$).
--
--   **Formalization Note**: $\overline{L}$ is `AlgebraicClosure L`, the perfect closure of $F$ in it is Mathlib's `perfectClosure F (AlgebraicClosure L)` (an intermediate field of $\overline{L}/F$, viewed as a field), $N_{L/F}$ is `Algebra.norm F`, the degree is `Module.finrank F L`, and "exponential characteristic $q$" is the instance `ExpChar F q`. The $C_1$ property of the perfect closure is written out as the hypothesis `hC1`: `f.totalDegree < n` and `MvPolynomial.constantCoeff f = 0` imply `∃ x : Fin n → perfectClosure F (AlgebraicClosure L), x ≠ 0 ∧ MvPolynomial.eval x f = 0` (the strong form of $C_1$, Lang's "quasi-algebraically closed", as in the Proved theorems `RatFunc.tsen_and_lang_C1` and `IsGalois.isMulCoboundary2_of_isPGroup_of_C1`).
-- source:
--   S. Lang, On quasi algebraic closure, Ann. of Math. (2) 55 (1952), 373-390, doi:10.2307/1969785; J.-P. Serre, Galois Cohomology, Springer 1997, doi:10.1007/978-3-642-59141-9, Chapter II, Section 3

import Mathlib

set_option autoImplicit false

theorem Algebra.norm_surjective_of_C1_perfectClosure
    (F : Type*) [Field F] (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (q : ℕ) [ExpChar F q] (hq : Nat.Coprime q (Module.finrank F L))
    (hC1 : ∀ (n : ℕ) (f : MvPolynomial (Fin n) (perfectClosure F (AlgebraicClosure L))),
      f.totalDegree < n → MvPolynomial.constantCoeff f = 0 →
        ∃ x : Fin n → perfectClosure F (AlgebraicClosure L), x ≠ 0 ∧ MvPolynomial.eval x f = 0) :
    Function.Surjective (Algebra.norm F : L → F) := by sorry
