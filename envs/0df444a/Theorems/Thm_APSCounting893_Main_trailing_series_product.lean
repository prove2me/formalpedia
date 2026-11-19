-- Prove2me | Theorems.Thm_APSCounting893_Main_trailing_series_product
-- name    : APSCounting893.Main.trailing_series_product
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T10:08:30.550519+00:00
-- url     : https://prove2.me/theorems/c54c01c9-804f-41c0-8e8f-34835a50ea42
-- title:
--   Trailing coefficient of a product of integral series roots
-- statement:
--   Let $p(t,T)\in\mathbb C[t,T]$, let $c(t)$ be a nonzero rational-exponent Hahn series, and let $a_i(t)$ be a finite family of Hahn series of nonnegative valuation. Let $\mu_i$ be nonnegative integer multiplicities. Suppose, as polynomials in $T$ over the Hahn-series field,
--
--   $$p(t,T)=c(t)\prod_i(T-a_i(t))^{\mu_i}.$$
--
--   Then there is a nonzero complex scalar $c_0$ such that
--
--   $$\operatorname{TC}_t p(T)=c_0\prod_i(T-a_i(0))^{\mu_i}.$$
--
--   Here $a_i(0)$ denotes the coefficient of exponent zero. This algebraic specialization step preserves multiplicities in the approximative characteristic polynomial.
-- source:
--   Agarwal, Hari, Pandey and Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, Section 5.1, Remark 5.1 and proof of Theorem 5.3, pp. 21–22, using Proposition 4.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_Resultant
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.trailing_series_product
    {ι : Type} (p : MvPolynomial (Fin 2) ℂ) (c : PuiseuxAmbient) (hc : c ≠ 0)
    (s : Finset ι) (x : ι → PuiseuxAmbient) (mu : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop)
    (hp : MvPolynomial.eval₂Hom (Polynomial.C.comp HahnSeries.C)
      (fun j : Fin 2 => if j = 0 then Polynomial.C (HahnSeries.single (1 : ℚ) (1 : ℂ)) else Polynomial.X) p =
        Polynomial.C c * ∏ i ∈ s, (Polynomial.X - Polynomial.C (x i)) ^ mu i) :
    ∃ a : ℂ, a ≠ 0 ∧ MvPolynomial.eval₂Hom Polynomial.C
      (fun j : Fin 2 => if j = 0 then 0 else Polynomial.X) (trailingCoefficient 0 p) =
        Polynomial.C a * ∏ i ∈ s, (Polynomial.X - Polynomial.C ((x i).coeff 0)) ^ mu i := by sorry
