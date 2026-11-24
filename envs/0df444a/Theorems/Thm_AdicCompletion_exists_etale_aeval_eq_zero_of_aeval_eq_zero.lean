-- Prove2me | Theorems.Thm_AdicCompletion_exists_etale_aeval_eq_zero_of_aeval_eq_zero
-- name    : AdicCompletion.exists_etale_aeval_eq_zero_of_aeval_eq_zero
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-24T05:18:40.995555+00:00
-- url     : https://prove2.me/theorems/23469a94-c9e1-4c35-b927-130d7faeed3f
-- title:
--   Artin approximation at a rational point: a formal solution of a polynomial system over a finite-type algebra has a solution with the same residues in an étale neighbourhood
-- statement:
--   Let $K$ be a perfect field, let $A$ be a $K$-algebra of finite type, and let $\chi : A \to K$ be a $K$-algebra homomorphism, that is, a $K$-rational point of $X = \operatorname{Spec} A$, with maximal ideal $\mathfrak{m} = \ker \chi$. Let $\hat{A} = \varprojlim_k A/\mathfrak{m}^k$ be the $\mathfrak{m}$-adic completion of $A$. Let $f_1, \dots, f_m \in A[Y_1, \dots, Y_n]$ be polynomials and let $\hat{y} = (\hat{y}_1, \dots, \hat{y}_n) \in \hat{A}^n$ be a formal solution of the system: $f_j(\hat{y}) = 0$ in $\hat{A}$ for $j = 1, \dots, m$.
--
--   Then the system has a solution with the same residues in an étale neighbourhood of the point $\chi$: there exist an étale $A$-algebra $R'$, a ring homomorphism $\chi' : R' \to K$ extending $\chi$ (so $\chi'(a) = \chi(a)$ for all $a \in A$), and $y = (y_1, \dots, y_n) \in R'^n$ such that
--
--   $$f_j(y) = 0 \text{ in } R' \quad (j = 1, \dots, m), \qquad \chi'(y_i) = \chi(a_i) \text{ for some } a_i \in A \text{ with } \hat{y}_i \equiv a_i \pmod{\mathfrak{m}\hat{A}} \quad (i = 1, \dots, n).$$
--
--   So $\chi'(y_i)$ is the residue of $\hat{y}_i$ in $\hat{A}/\mathfrak{m}\hat{A} = A/\mathfrak{m} = K$. Since the henselization of $A$ at $\mathfrak{m}$ is the colimit of the étale neighbourhoods $(R', \chi')$, this says that a system of polynomial equations that is solvable in the completion is solvable in the henselization with the same residues.
--
--   This is M. Artin's approximation theorem (1969, Theorem 1.10) at a rational point of a variety, in its étale-neighbourhood form and to first order. Artin's theorem holds over any field and also gives approximation to any order $c$ ($y_i \equiv \hat{y}_i$ modulo $\mathfrak{m}^c$); the statement here is the order-one case over a perfect field.
--
--   **Formalization Note**: $K$ is a field with `[PerfectField K]`, and $A$ is a commutative ring with `[Algebra K A]` and `[Algebra.FiniteType K A]`. The point is `χ : A →ₐ[K] K` and $\mathfrak{m}$ is `RingHom.ker χ`; $\hat{A}$ is `AdicCompletion (RingHom.ker χ) A` with its `A`-algebra structure. The system is `f : Fin m → MvPolynomial (Fin n) A` and the formal solution is `ŷ : Fin n → AdicCompletion (RingHom.ker χ) A` with `MvPolynomial.aeval ŷ (f j) = 0` for all `j`. The conclusion provides a type `R'` with `CommRing R'`, `Algebra A R'` and `Algebra.Etale A R'`, a ring homomorphism `χ' : R' →+* K` with `χ' (algebraMap A R' a) = χ a` for all `a : A`, and `y : Fin n → R'` with `MvPolynomial.aeval y (f j) = 0` for all `j`. The residue condition is: for each `i` there is `a : A` with `χ' (y i) = χ a` and `AdicCompletion.evalₐ (RingHom.ker χ) 1 (ŷ i) = Ideal.Quotient.mk _ a`, where `AdicCompletion.evalₐ (RingHom.ker χ) 1` is the projection $\hat{A} \to A/\mathfrak{m}^1$. All types live in `Type`. The statement is not vacuous: the homomorphism `χ'` to the field `K` rules out the zero ring for `R'`. For example, with `K = ℚ`, `A = ℚ[t]`, `χ` the evaluation at `t = 0` and the single equation $Y^2 - (1 + t) = 0$, the formal solution $\hat{y} = \sqrt{1 + t} \in \mathbb{Q}[[t]]$ has no solution in $A$ itself, but it has one in an étale neighbourhood, with residue $1$.
-- source:
--   M. Artin, Algebraic approximation of structures over complete local rings, Publ. Math. IHÉS 36 (1969), 23–58, Theorem 1.10

import Mathlib

set_option autoImplicit false

theorem AdicCompletion.exists_etale_aeval_eq_zero_of_aeval_eq_zero
    (K : Type) [Field K] [PerfectField K] (A : Type) [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (χ : A →ₐ[K] K) (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) A)
    (ŷ : Fin n → AdicCompletion (RingHom.ker χ) A) (hŷ : ∀ j, MvPolynomial.aeval ŷ (f j) = 0) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra A R') (_ : Algebra.Etale A R') (χ' : R' →+* K)
      (y : Fin n → R'), (∀ a : A, χ' (algebraMap A R' a) = χ a) ∧ (∀ j, MvPolynomial.aeval y (f j) = 0) ∧
      ∀ i, ∃ a : A, χ' (y i) = χ a ∧ AdicCompletion.evalₐ (RingHom.ker χ) 1 (ŷ i) = Ideal.Quotient.mk _ a := by
  sorry
