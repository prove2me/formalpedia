-- Prove2me | Theorems.Thm_APSCounting893_Main_input_reduction_nonvanishing_certificate
-- name    : APSCounting893.Main.input_reduction_nonvanishing_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:08:47.904494+00:00
-- url     : https://prove2.me/theorems/2bd1a7af-e1f6-4c77-805a-26050e8c0761
-- title:
--   Nonvanishing certificate for the input reduction
-- statement:
--   Let $F:\mathbb C^n\to\mathbb C^m$ have nonconstant coordinate polynomials, image-closure dimension $1\le r<m$, and maximum coordinate degree $d\ge1$. The sampled coefficients comprise $n-r$ affine linear equations on the domain and $r+1$ linear combinations of the outputs. There is a nonzero complex polynomial $P$ in these coefficients with
--
--   $$\deg P\le2(n-r)d^m+(r+1)d^r$$
--
--   such that every rational coefficient tuple $s$ with $P(s)\ne0$ admits the selected rational affine parametrization, produces an image closure of dimension $r$, and preserves APS in both directions. When $m=r+1$, the sampled output coefficients are ignored, as in the source construction.
--
--   This algebraic exceptional-set certificate separates the geometric input-reduction argument from the finite-grid probability estimate in Proposition 3.14. It applies to every rational tuple, independently of the sampling grid.
--
--   **Formalization Note** The coefficients are enumerated by the canonical finite equivalence from the domain-equation and output-projection labels to an initial segment of the natural numbers. Successful parametrization, the composed projected polynomial map, its image dimension, and APS preservation are precisely the existing mission definitions.
-- source:
--   Agarwal, Hari, Pandey and Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, Proposition 3.14 and its proof, p.14, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf; the two exceptional-locus bounds are the generic-fiber affine-section bound from Lemma 3.12 and the projective projection bound of Theorem 3.13 (Guo, Saxena and Sinhababu 2019, Theorem 4.6, pp.18–21).

import Definitions.Def_APSCounting893_Main_RandomReduction
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.input_reduction_nonvanishing_certificate
    (n m r : ℕ) (F : PolynomialMap ℂ n m)
    (hnonconstant : ∀ i, 0 < (F i).totalDegree)
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞))
    (hr : 1 ≤ r) (hrm : r < m) :
    ∃ p : MvPolynomial (Fin (Fintype.card (ReductionLabels n m r))) ℂ,
      p ≠ 0 ∧ p.totalDegree ≤ 2 * (n-r) * inputDegree F ^ m + (r+1) * inputDegree F ^ r ∧
      ∀ s : ReductionLabels n m r → ℚ,
        MvPolynomial.eval (fun j => (s ((Fintype.equivFin (ReductionLabels n m r)).symm j) : ℂ)) p ≠ 0 →
          ReductionSucceeds F s := by sorry
