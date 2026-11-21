-- Prove2me | Theorems.Thm_ConnesRZ_archTerm_eq_neg_setIntegral_of_apply_zero
-- name    : ConnesRZ.archTerm_eq_neg_setIntegral_of_apply_zero
-- status  : Proved
-- author  : @smmercuri
-- created : 2026-11-20T22:28:31.49523+00:00
-- url     : https://prove2.me/theorems/c15148eb-fc69-41b9-a253-8689c6029283
-- title:
--   Archimedean term of the Weil distribution as a real integral, for tests vanishing at the identity
-- statement:
--   Let $g:\mathbb R\to\mathbb C$ be smooth and compactly supported, viewed as a test function on $\mathbb R_{>0}^\times$ through $u=e^{t}$, and assume $g(0)=0$ (the test vanishes at the identity $u=1$). Write
--   $$\widehat g(z)=\int_{\mathbb R} g(t)\,e^{(z-\frac12)t}\,dt .$$
--   The archimedean term of the Weil distribution is
--   $$W_\infty(g)=\frac1{2\pi}\int_{\mathbb R}\widehat g\!\left(\tfrac12+ir\right)\Big(\operatorname{Re}\psi\!\left(\tfrac14+\tfrac{ir}{2}\right)-\log\pi\Big)\,dr,\qquad \psi=\Gamma'/\Gamma .$$
--   Then the function $x\mapsto \big(g(x)+g(-x)\big)\dfrac{e^{-x/2}}{1-e^{-2x}}$ is integrable on $(0,\infty)$, and
--   $$
--   W_\infty(g)=-\int_0^\infty \big(g(x)+g(-x)\big)\,\frac{e^{-x/2}}{1-e^{-2x}}\,dx .
--   $$
--
--   This identifies the digamma (spectral) form of the archimedean term with Connes' geometric local term at the real place, $\int_{\mathbb R^\times} h(u^{-1})\,|1-u|^{-1}\,d^\times u$ with $h(u)=g(\log|u|)$, on the hyperplane of test functions vanishing at $1$, where no principal value or constant correction is needed. It converts the explicit formula `ConnesRZ.explicit_formula_C2` into the form of the local trace formulas.
--
--   **Formalization Note** The test-function class is `ConnesRZ.IsTest` (smooth, compactly supported, complex valued on $\mathbb R$), and $W_\infty$ is `ConnesRZ.archTerm`, whose bracket is written with `logDeriv Complex.Gamma`.
-- source:
--   A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Selecta Math. (N.S.) 5 (1999), arXiv:math/9811068v1, §VI eqs. (15)–(16), p. 27, and Appendix, Theorem 6, p. 77 (real place, test functions with h(1)=0); the digamma form is the Gamma-factor term of the Weil explicit formula as encoded in ConnesRZ.archTerm (Connes eq. (12) normalization).

import Definitions.Def_ConnesRZ_weil_defs

set_option autoImplicit false

open Complex MeasureTheory Set ConnesRZ

theorem ConnesRZ.archTerm_eq_neg_setIntegral_of_apply_zero (g : ℝ → ℂ) (hg : IsTest g)
    (hg0 : g 0 = 0) :
    IntegrableOn (fun x : ℝ => (g x + g (-x)) *
      ((Real.exp (-x / 2) / (1 - Real.exp (-2 * x)) : ℝ) : ℂ)) (Ioi 0) ∧
    archTerm g = -∫ x in Ioi (0 : ℝ), (g x + g (-x)) *
      ((Real.exp (-x / 2) / (1 - Real.exp (-2 * x)) : ℝ) : ℂ) := by sorry
