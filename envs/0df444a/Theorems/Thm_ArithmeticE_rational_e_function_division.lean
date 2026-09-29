-- Prove2me | Theorems.Thm_ArithmeticE_rational_e_function_division
-- name    : ArithmeticE.rational_e_function_division
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T16:09:32.871672+00:00
-- url     : https://prove2.me/theorems/9eae34ed-154a-41d0-adc3-792a1d5e546a
-- title:
--   Classical division theorem for rational-coefficient E-functions
-- statement:
--   Let $f(X)=\sum_{n\ge0}a_nX^n/n!$ have rational normalized coefficients satisfying the E-function exponential size and common-denominator bounds. Suppose $f(1)=0$ and $f$ is annihilated by a nonzero rational polynomial differential operator $\sum_{k=0}^m p_k(X)D^k$, with $p_m\ne0$.
--
--   There exists a formal series $g$ such that $(1-X)g=f$, the factorial-normalized coefficients of $g$ satisfy the same rational arithmetic conditions, and $g$ is annihilated by a rational polynomial differential operator of order $m$ with nonzero leading coefficient. Thus division by $1-X$ at the zero $1$ preserves the rational-coefficient E-function conditions.
--
--   The transformed coefficients are $q_k=(1-X)p_k-(k+1)p_{k+1}$ for $k<m$, and $q_m=(1-X)p_m$. The value-zero hypothesis is expressed as a convergent real series identity, which is appropriate for rational coefficients at $1$. No arithmetic regularity or value-lifting theorem is assumed.
-- source:
--   Beukers, A refined version of the Siegel–Shidlovskii theorem, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, proof of Corollary 2.2, pp. 3–4. This proves preservation of the rational E-function conditions under division at the zero 1; it does not invoke or prove the later minimal-operator regularity assertion.

import Definitions.Def_rationalEArithmetic
open ArithmeticE PowerSeries

theorem ArithmeticE.rational_e_function_division (a : ℕ → ℚ) (ha : RationalArithmetic a)
    (hz : HasSum (fun n : ℕ => (a n:ℝ)/(n.factorial:ℝ)) 0)
    (p : ℕ → Polynomial ℚ) (m : ℕ) (hp : p m ≠ 0)
    (hode : ∑ k ∈ Finset.range (m+1), ((p k).map (algebraMap ℚ ℂ):PowerSeries ℂ)*
      (PowerSeries.derivative ℂ)^[k] (PowerSeries.mk (fun n => (a n:ℂ)/(n.factorial:ℂ)))=0) :
    ∃ g : PowerSeries ℂ, RationalSeriesArithmetic g ∧
      (1-PowerSeries.X)*g=PowerSeries.mk (fun n => (a n:ℂ)/(n.factorial:ℂ)) ∧
      ∃ q : ℕ → Polynomial ℚ, q m ≠ 0 ∧
        ∑ k ∈ Finset.range (m+1), ((q k).map (algebraMap ℚ ℂ):PowerSeries ℂ)*
          (PowerSeries.derivative ℂ)^[k] g=0 := by sorry
