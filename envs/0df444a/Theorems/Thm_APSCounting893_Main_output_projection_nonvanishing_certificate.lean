-- Prove2me | Theorems.Thm_APSCounting893_Main_output_projection_nonvanishing_certificate
-- name    : APSCounting893.Main.output_projection_nonvanishing_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T13:23:31.403473+00:00
-- url     : https://prove2.me/theorems/cfcab3cc-5320-4067-bce1-989bfc56403f
-- title:
--   Output-projection certificate preserving dimension and APS
-- statement:
--   Let $F:\mathbb C^n\to\mathbb C^m$ be a polynomial map with image closure of dimension $1\le r<m$. Set $d=\max(1,\deg f_i)$. There is a nonzero polynomial $p$ in the entries of an $(r+1)\times m$ coefficient matrix such that
--
--   $$\deg p\le (r+1)d^r.$$
--
--   For every rational matrix $A$ with $p(A)\ne0$, let $G=AF$. Then
--
--   $$\dim\overline{G(\mathbb C^n)}^{\mathrm{Zar}}=r,\qquad
--   0\in\overline{F(\mathbb C^n)}^{\mathrm{Zar}}\ \Longleftrightarrow\ 0\in\overline{G(\mathbb C^n)}^{\mathrm{Zar}}.$$
--
--   This is the geometric nonvanishing certificate behind the output-reduction probability bound in Theorem 3.13 and Proposition 3.14. Nonvanishing over a finite rational grid yields the stated exceptional probability by the polynomial zero bound.
-- source:
--   Agarwal, Hari, Pandey and Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, Theorem 3.13 and Proposition 3.14, pp.13–14, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf; the projective avoidance argument is Guo, Saxena and Sinhababu, Algebraic Dependencies and PSPACE Algorithms in Approximative Complexity, Theory of Computing 15(16), 2019, Theorem 4.6 and Lemmas 4.7–4.12, pp.18–21, https://theoryofcomputing.org/articles/v015a016/v015a016.pdf; Chow-form incidence and multidegree: Jeronimo, Krick, Sabia and Sombra, The computational complexity of the Chow form, arXiv:math/0210009, Section 1.1, pp.6–7, https://arxiv.org/pdf/math/0210009.

import Definitions.Def_APSCounting893_Main_RandomReduction
set_option autoImplicit false
open MvPolynomial

theorem APSCounting893.Main.output_projection_nonvanishing_certificate
    {n m r : ℕ} (F : APSCounting893.Main.PolynomialMap ℂ n m)
    (hrpos : 0 < r) (hrm : r < m)
    (hdim : RSCapacity.algDim (APSCounting893.Main.imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞)) :
    ∃ p : MvPolynomial (Fin (r+1) × Fin m) ℂ,
      p ≠ 0 ∧ p.totalDegree ≤ (r+1)*(APSCounting893.Main.inputDegree F)^r ∧
      ∀ A : Fin (r+1) × Fin m → ℚ,
        eval (fun a => (A a : ℂ)) p ≠ 0 →
        RSCapacity.algDim (APSCounting893.Main.imageClosure
          (fun i : Fin (r+1) => ∑ j : Fin m, MvPolynomial.C (A (i,j) : ℂ) * F j)) = ((r : ℕ∞) : WithBot ℕ∞) ∧
        (APSCounting893.Main.hasAPS F ↔ APSCounting893.Main.hasAPS
          (fun i : Fin (r+1) => ∑ j : Fin m, MvPolynomial.C (A (i,j) : ℂ) * F j)) := by sorry
