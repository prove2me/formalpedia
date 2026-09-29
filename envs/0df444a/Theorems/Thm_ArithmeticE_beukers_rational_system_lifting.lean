-- Prove2me | Theorems.Thm_ArithmeticE_beukers_rational_system_lifting
-- name    : ArithmeticE.beukers_rational_system_lifting
-- status  : Open
-- author  : @shivm
-- created : 2026-09-11T15:53:31.057292+00:00
-- url     : https://prove2.me/theorems/26ac9840-f286-42f0-ae30-36d7b0ac59f6
-- title:
--   Classical Beukers linear lifting for rational-coefficient E-systems
-- statement:
--   Let $f_1,\ldots,f_m$ be formal series with rational factorial-normalized coefficients satisfying exponential size and common-denominator bounds. Suppose
--   $$T(X)f'(X)=B(X)f(X),$$
--   with $T\in\mathbb Q[X]$ and $B\in M_m(\mathbb Q[X])$. At an algebraic complex number $\xi$ with $\xi T(\xi)\ne0$, every algebraic linear relation $\sum_i a_i f_i(\xi)=0$ lifts to polynomials $p_i\in\mathbb C[X]$ such that
--   $$\sum_i p_i(X)f_i(X)=0,\qquad p_i(\xi)=a_i.$$
--   This is a rational-coefficient instance of Beukers' established theorem, not a conjecture. The conclusion only asks for complex polynomial coefficients; the classical result supplies algebraic ones. The remaining task is to formalize the general arithmetic specialization argument.
-- source:
--   Beukers, A refined version of the Siegel–Shidlovskii theorem, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, pp. 1–6, especially Corollary 2.2 and Theorem 3.2. Explicit specialization and arithmetic verification for the Euler system.

import Definitions.Def_rationalEArithmetic
open ArithmeticE

theorem ArithmeticE.beukers_rational_system_lifting
    (m : ℕ) (f : Fin m → PowerSeries ℂ)
    (T : Polynomial ℚ) (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (harith : ∀ i, RationalSeriesArithmetic (f i))
    (hode : ∀ i, (T.map (algebraMap ℚ ℂ):PowerSeries ℂ)*PowerSeries.derivative ℂ (f i) =
      ∑ j, ((B i j).map (algebraMap ℚ ℂ):PowerSeries ℂ)*f j)
    (ξ : ℂ) (hξ : IsAlgebraic ℚ ξ)
    (hreg : ξ*T.eval₂ (algebraMap ℚ ℂ) ξ ≠ 0)
    (a : Fin m → ℂ) (ha : ∀ i, IsAlgebraic ℚ (a i))
    (hrel : ∑ i, a i*seriesValue (f i) ξ=0) :
    ∃ p : Fin m → Polynomial ℂ,
      (∑ i, (p i:PowerSeries ℂ)*f i=0) ∧ ∀ i, (p i).eval ξ=a i := by sorry
