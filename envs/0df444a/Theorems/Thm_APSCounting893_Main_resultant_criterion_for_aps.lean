-- Prove2me | Theorems.Thm_APSCounting893_Main_resultant_criterion_for_aps
-- name    : APSCounting893.Main.resultant_criterion_for_aps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:25:36.368419+00:00
-- url     : https://prove2.me/theorems/815a851b-53df-4a62-9a3c-e6650d3946e3
-- title:
--   Theorem 5.3 — Resultant criterion for APS
-- statement:
--   In the admissible reduced-map setup, choose $\ell$ injective on $Y_0\cup\{0\}$ and use the actual resultant of the source homogenizations and perturbations. There are $c\in\mathbb C^\times$ and strictly positive integers $M_y$ such that
--
--   $$R_\ell(T)=\mathrm{TC}_t\mathrm{TC}_w\mathrm{TC}_{\epsilon}R=c\prod_{y\in Y_0}(T-\ell(y))^{M_y},\qquad M_y>0.$$
--   $$\operatorname{APS}(F)\iff R_\ell(0)=0.$$
--
--   Both the full factorization and the equivalence are conclusions. The finite product ranges over the entire actual zero fiber, and no order of specialization or trailing extraction is interchanged.
--
--   Differences from the source:
--   - encoding: the product over the finite zero fiber and three trailing extractions → a finite set equal to the actual zero fiber, positive natural multiplicities, and coefficient extraction in epsilon, w, t order; reason: retains the full product and both directions of the APS equivalence
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Theorem 5.3, p. 22, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_Resultant

set_option autoImplicit false

namespace APSCounting893.Main

theorem resultant_criterion_for_aps (F : ReducedMap) (D : LineData F) (lambda : Affine ℂ (F.n + 1))
    (hsep : Set.InjOn (separatingForm lambda) (zeroFiber F D.c ∪ {0}))
    (degrees : Fin (F.n + (F.n + 1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees) :
    ∃ (S : Finset (Affine ℂ (F.n + 1))) (c : ℂ) (M : Affine ℂ (F.n + 1) → ℕ),
      (S : Set _) = zeroFiber F D.c ∧ c ≠ 0 ∧ (∀ y ∈ S, 0 < M y) ∧
      resultantCriterion (resultantFor F D.c D.alpha lambda degrees) =
        Polynomial.C c * ∏ y ∈ S,
          (Polynomial.X - Polynomial.C (separatingForm lambda y)) ^ M y ∧
      (hasAPS F.F ↔ (resultantCriterion (resultantFor F D.c D.alpha lambda degrees)).eval 0 = 0) := by sorry

end APSCounting893.Main
