-- Prove2me | Theorems.Thm_APSCounting893_Main_Supplement_integral_iff_bounded_branches
-- name    : APSCounting893.Main.Supplement.integral_iff_bounded_branches
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:12:47.969328+00:00
-- url     : https://prove2.me/theorems/ee09e4e5-7fd1-40a1-b8c8-54aeb448ccab
-- title:
--   Corollary 7.6 — Integrality iff every algebraic branch is bounded
-- statement:
--   Let $f,f_1,\ldots,f_m\in\mathbb C[x_1,\ldots,x_n]$ and $A=\mathbb C[f_1,\ldots,f_m]$. In a fixed algebraic closure of $\mathbb C(t)$ with extended $t$-adic valuation,
--
--   $$f\text{ integral over }A\quad\Longleftrightarrow\quad\forall\beta\in\overline{\mathbb C(t)}^n,\ \bigl[\forall i,\ \operatorname{val}_t f_i(\beta)\ge0\bigr]\Longrightarrow\operatorname{val}_t f(\beta)\ge0.$$
--
--   The input coordinates may have negative valuation. Zero evaluations have valuation $+\infty$ and satisfy nonnegativity. This is the algebraic-branch boundedness criterion supporting Theorem 7.8.
--
--   Differences from the source:
--   - encoding: the algebraic closure of C(t) with its extended t-adic valuation → the algebraic part of the published Puiseux field, defined by a nonzero C[t][X] relation, with series orderTop; reason: a fixed Puiseux realization of the algebraic closure represents every algebraic branch; denominator clearing changes no algebraic element and zero has order infinity
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Corollary 7.6, p. 30

import Definitions.Def_APSCounting893_Main_Supplement_Certificates

set_option autoImplicit false

namespace APSCounting893.Main.Supplement

/-- Corollary 7.6. Algebraic branches of C(t), with their extended t-adic valuation,
are realized in a fixed Puiseux closure. Inputs need not belong to the valuation ring. -/
theorem integral_iff_bounded_branches (n m : ℕ) (F : PolynomialMap ℂ n m)
    (f : Polynomials ℂ n) :
    IntegralOverGenerators F f ↔
      ∀ beta : Affine PuiseuxAmbient n, (∀ j, IsAlgebraicBranch (beta j)) →
        (∀ i, 0 ≤ (MvPolynomial.eval₂ HahnSeries.C beta (F i)).orderTop) →
        0 ≤ (MvPolynomial.eval₂ HahnSeries.C beta f).orderTop := by sorry

end APSCounting893.Main.Supplement
