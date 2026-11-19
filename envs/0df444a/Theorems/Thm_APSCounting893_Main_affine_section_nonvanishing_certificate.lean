-- Prove2me | Theorems.Thm_APSCounting893_Main_affine_section_nonvanishing_certificate
-- name    : APSCounting893.Main.affine_section_nonvanishing_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T13:11:20.169094+00:00
-- url     : https://prove2.me/theorems/8de604f2-8c53-4ab0-9644-df270444a7bc
-- title:
--   Affine-section certificate preserving the polynomial image closure
-- statement:
--   Let $F:\mathbb C^n\to\mathbb C^m$ be a polynomial map with image closure $Y$ of dimension $r<m$, and put $d=\max(1,\deg f_i)$. There is a nonzero polynomial $q$ in the coefficients of $n-r$ affine equations such that
--
--   $$\deg q\le 2(n-r)d^m.$$
--
--   Whenever rational coefficients $s$ satisfy $q(s)\ne0$, their affine equations define an $r$-dimensional plane admitting a rational affine parametrization. For every affine parametrization selected by the section predicate, the restriction of $F$ has exactly the original image closure:
--
--   $$\overline{F|_H(\mathbb C^r)}^{\mathrm{Zar}}=Y.$$
--
--   This is the domain-reduction certificate used in Proposition 3.14. It preserves the entire image closure and therefore preserves both its dimension and APS. The output-projection coefficients are unrestricted in this statement.
--
--   **Formalization Note** The output count is written as $m+1$ in Lean to expose its positive size. The selected rational parametrization is the same epsilon-selected object used by the mission's input-reduction definition.
-- source:
--   Agarwal, Hari, Pandey and Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, Proposition 3.14 and proof, pp.14–15 (domain/input reduction using generic affine sections), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_RandomReduction
set_option autoImplicit false
open MvPolynomial

theorem APSCounting893.Main.affine_section_nonvanishing_certificate {n m r : ℕ} (F : PolynomialMap ℂ n (m+1))
    (hrm : r < m+1)
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞)) :
    ∃ q : MvPolynomial ((Fin (n-r) × Fin (n+1))) ℂ,
      q ≠ 0 ∧ q.totalDegree ≤ 2*(n-r)*(inputDegree F)^(m+1) ∧
      ∀ s : ReductionLabels n (m+1) r → ℚ,
        eval (fun a => (s (Sum.inl a) : ℂ)) q ≠ 0 →
        ParametrizesSection s (selectedSectionParameter s) ∧
        imageClosure ((fun i => MvPolynomial.eval₂Hom MvPolynomial.C (parameterMap (selectedSectionParameter s)) (F i))) = imageClosure F := by sorry
