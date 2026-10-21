-- Prove2me | Theorems.Thm_FiniteFields_zetaFunction_integral_presentation
-- name    : FiniteFields.zetaFunction_integral_presentation
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T07:32:20.668834+00:00
-- url     : https://prove2.me/theorems/de98b577-83c1-4a94-b343-23d34d7c338a
-- title:
--   Integral presentation of the zeta function of a projective variety over a finite field: $Z(X,T)=A(T)/B(T)$ with $A,B\in\mathbb{Z}[T]$, $A(0)=B(0)=1$
-- statement:
--   Let $k=\mathbb{F}_q$ be a finite field of characteristic $p$, and let $X$ be a projective scheme over $k$, i.e. $X$ admits a closed immersion into some projective space $\mathbb{P}^N_k$ over $k$. For $m\ge1$ let $N_m$ be the number of $\mathbb{F}_{q^m}$-points of $X$, that is, of morphisms $\operatorname{Spec}\mathbb{F}_{q^m}\to X$ over $\operatorname{Spec}k$, where $\mathbb{F}_{q^m}$ is the extension of $k$ of degree $m$. The zeta function of $X$ is the formal power series
--   $$
--   Z(X,T)=\exp\Big(\sum_{m\ge1}\frac{N_m}{m}\,T^m\Big)\in\mathbb{Q}[[T]].
--   $$
--
--   **Theorem.** There exist polynomials $A,B\in\mathbb{Z}[T]$ such that
--
--   1. $A(0)=1$ and $B(0)=1$;
--   2. $A$ and $B$ are coprime in $\mathbb{Q}[T]$;
--   3. $$Z(X,T)\cdot B(T)=A(T)\qquad\text{in }\mathbb{Q}[[T]].$$
--
--   In other words, the zeta function is a rational function whose reduced form has **integer** coefficients and constant terms $1$. This strengthens Dwork's rationality theorem, which gives $Z(X,T)\in\mathbb{Q}(T)$. It is the integrality statement that turns rationality into the shape required by the Weil conjectures: together with the separation of the inverse roots by their absolute values, it is what makes the factors $P_i(T)$ of $Z(X,T)$ polynomials with integer coefficients.
--
--   **Formalization Note.** Projectivity is the platform's `IsProjectiveOver k f` for the structure morphism $f$, and $Z(X,T)$ is the platform's `zetaFunction p f`. Smoothness and geometric irreducibility are not assumed. Polynomials over $\mathbb{Z}$ are mapped to $\mathbb{Q}[T]$ by `Int.castRingHom ℚ` and viewed in $\mathbb{Q}[[T]]$ by the canonical coercion. Coprimality means that there are $U,V\in\mathbb{Q}[T]$ with $UA+VB=1$.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648 (rationality: §4, complement to Theorem 2, and §5, Application 2); P. Fatou, *Séries trigonométriques et séries de Taylor*, Acta Math. 30 (1906), 335–400 (Fatou's lemma: a power series with integer coefficients that represents a rational function is a quotient of polynomials with integer coefficients and constant term 1); integrality of $Z(X,T)$ from the Euler product $Z(X,T)=\prod_{x}(1-T^{\deg x})^{-1}$ over the closed points of $X$. Lean: `Bridge/IntegralPresentation.lean`, `Bridge/EulerProduct.lean`, `Bridge/ClosedPoints.lean`, `Bridge/Fatou.lean` of the WeilConjecture project, using the platform node `FiniteFields.dwork_rationality_explicit`.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

theorem FiniteFields.zetaFunction_integral_presentation (p : ℕ) [Fact p.Prime] (k : Type)
    [Field k] [Finite k] [CharP k p] (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    (hproj : IsProjectiveOver k f) :
    ∃ A B : ℤ[X], A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧
      IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) ∧
      zetaFunction p f * ((B.map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) =
        ((A.map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) := by sorry
