-- Prove2me | Theorems.Thm_DenseProdQSAT_Testing_homogeneous_common_root
-- name    : DenseProdQSAT.Testing.homogeneous_common_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:10.344131+00:00
-- url     : https://prove2.me/theorems/d18d2e91-f579-47ce-b641-4522b4e7e812
-- title:
--   Lemma 4.9 — uniform homogeneous common-root criterion
-- statement:
--   Fix $d\ge1$, $N\ge1$, a number $s$ of equations, and a degree profile $e_1,\ldots,e_s$ with $0\le e_j\le N$. There exists one real polynomial $P$ on the real and imaginary coefficient coordinates such that
--
--   $$\deg P\le2\binom{dN}{d-1},\qquad P(\gamma)\ge0\quad\text{for every real coefficient vector }\gamma.$$
--
--   For every family of complex polynomials $f_j$ homogeneous of degree $e_j$, let $\gamma(f)$ list its coefficients. Then
--
--   $$P(\gamma(f))=0\iff\exists v\in\mathbb C^d\setminus\{0\},\ \forall j,\ f_j(v)=0.$$
--
--   Zero polynomials and degree-zero equations are included. The polynomial is chosen before the coefficient values, so it gives a reusable elimination criterion for the parameter families on pp. 17–18.
--
--   Differences from the source:
--   - reading: a polynomial in the coefficient vector gamma of the given homogeneous system → one polynomial working for all coefficient values at each fixed number of variables, equation count and homogeneous degree profile; reason: the use under polynomial substitution on pp. 17–18 requires this uniform interpretation; choosing 0 or 1 after deciding root existence would lose the result
--   - encoding: a real vector listing complex coefficients in a fixed order → coordinates indexed by equation, monomial of degree at most N, and real or imaginary component; reason: fixed finite coefficient indexing is a relabeling and includes zero slots for absent monomials
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), Lemma 4.9, p. 14

import Definitions.Def_DenseProdQSAT_Testing_Algebra
set_option autoImplicit false

namespace DenseProdQSAT.Testing

theorem homogeneous_common_root (d s N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (degrees : Fin s → ℕ) (hdegrees : ∀ j, degrees j ≤ N) :
    ∃ P : MvPolynomial (CoefficientIndex d s N) ℝ,
      P.totalDegree ≤ 2 * (d * N).choose (d - 1) ∧
      (∀ γ : CoefficientIndex d s N → ℝ, 0 ≤ MvPolynomial.eval γ P) ∧
      ∀ f : Fin s → MvPolynomial (Fin d) ℂ,
        (∀ j, (f j).IsHomogeneous (degrees j)) →
        (MvPolynomial.eval (CoefficientVector f) P = 0 ↔
          ∃ v : Fin d → ℂ, v ≠ 0 ∧ ∀ j, MvPolynomial.eval v (f j) = 0) := by sorry

end DenseProdQSAT.Testing
