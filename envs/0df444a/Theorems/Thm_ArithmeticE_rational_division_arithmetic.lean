-- Prove2me | Theorems.Thm_ArithmeticE_rational_division_arithmetic
-- name    : ArithmeticE.rational_division_arithmetic
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:57:09.572851+00:00
-- url     : https://prove2.me/theorems/a58de5e6-f17f-4450-8691-691a282f6396
-- title:
--   Arithmetic coefficient bounds survive division of a rational E-series at a zero
-- statement:
--   Suppose rational coefficients $a_n$ satisfy the E-function exponential size and common-denominator bounds, and $\sum_{n\ge0}a_n/n!=0$. Then
--   $$b_n=n!\sum_{k=0}^n\frac{a_k}{k!}$$
--   satisfy the same kind of arithmetic bounds. Every common denominator for $a_0,\ldots,a_n$ also clears $b_0,\ldots,b_n$. Exponential size follows by writing the partial sum as a tail and comparing factorials. This is the arithmetic coefficient part of the classical E-function division theorem, fully proved here for rational coefficients.
-- source:
--   Beukers, A refined version of the Siegel–Shidlovskii theorem, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, proof of Corollary 2.2, pp. 3–4. This formalization proves the rational arithmetic division step without invoking André or Beukers specialization.

import Definitions.Def_rationalEArithmetic
open ArithmeticE

theorem ArithmeticE.rational_division_arithmetic (a : ℕ → ℚ) (ha : RationalArithmetic a)
    (hz : HasSum (fun n : ℕ => (a n:ℝ)/(n.factorial:ℝ)) 0) :
    RationalArithmetic (fun n => (n.factorial:ℚ)*∑ k ∈ Finset.range (n+1), a k/(k.factorial:ℚ)) := by sorry
