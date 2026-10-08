-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_deriv_ne_zero_of_injOn
-- name    : AhlforsComplexAnalysis.deriv_ne_zero_of_injOn
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T11:43:22.026986+00:00
-- url     : https://prove2.me/theorems/d00c6b28-0e54-44e6-8a20-e7187c95b4ca
-- title:
--   An injective analytic function has nonzero derivative
-- statement:
--   Let $f$ be a complex function that is analytic at a point $c\in\mathbb C$ and injective on some neighbourhood $U$ of $c$. Then
--
--   $$f'(c)\neq 0 .$$
--
--   In other words, an analytic function cannot have a critical point at a place where it is locally injective. In one complex variable this is the reason that an injective holomorphic map is automatically conformal and that its inverse is again holomorphic, and it is the step that lets one pass from a bijective holomorphic map between plane regions to a biholomorphism. It is used here for the uniqueness half of the Riemann mapping theorem.
--
--   **Formalization Note.** `f : ℂ → ℂ` is only assumed analytic at the single point `c` (`AnalyticAt ℂ f c`), while injectivity is assumed on the neighbourhood `U` (`Set.InjOn f U`, with `U ∈ nhds c`); `deriv` is Mathlib's complex derivative.
-- source:
--   Standard fact of one complex variable. See T. Tao, 246A Notes 5: conformal mapping, https://terrytao.wordpress.com/2016/10/18/246a-notes-5-conformal-mapping/ (which cites Exercise 41 of 246A Notes 4 for holomorphy of the inverse of an injective holomorphic map); also Ahlfors, Complex Analysis, 3rd ed., Ch. 4 section 3.3 (local mapping).

import Mathlib

namespace AhlforsComplexAnalysis

theorem deriv_ne_zero_of_injOn {f : ℂ → ℂ} {c : ℂ} {U : Set ℂ} (hU : U ∈ nhds c)
    (hf : AnalyticAt ℂ f c) (hinj : Set.InjOn f U) : deriv f c ≠ 0 := by sorry

end AhlforsComplexAnalysis
