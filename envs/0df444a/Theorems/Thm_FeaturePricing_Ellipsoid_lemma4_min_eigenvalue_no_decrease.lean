-- Prove2me | Theorems.Thm_FeaturePricing_Ellipsoid_lemma4_min_eigenvalue_no_decrease
-- name    : FeaturePricing.Ellipsoid.lemma4_min_eigenvalue_no_decrease
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:33:15.400972+00:00
-- url     : https://prove2.me/theorems/ff60b74b-e4cf-4c5e-bf30-86ad92a43c36
-- title:
--   Lemma 4, p. 18 — with k = 1/(400d²), λ_d(A) ≤ kε² and x′Ax > ε²/4 imply λ_d(Ã) ≥ λ_d(A)
-- statement:
--   Let $d\ge2$, $\epsilon>0$, $k=\frac1{400d^2}$, let $A$ be a positive definite $d\times d$ matrix and $x\in\mathbb R^d$ with $\|x\|\le1$ (Euclidean norm). Let $\tilde A$ be the update (4) of $A$ along $x$. If
--   $$
--   \lambda_d(A)\le k\epsilon^2\qquad\text{and}\qquad x'Ax>\tfrac14\epsilon^2,
--   $$
--   then
--   $$
--   \lambda_d(\tilde A)\ge\lambda_d(A),
--   $$
--   i.e. the smallest eigenvalue does not decrease after the update.
--
--   The condition $x'Ax>\frac14\epsilon^2$ is exactly the exploration test $\bar b_t-\underline b_t=2\sqrt{x_t'A_tx_t}>\epsilon$ of EllipsoidPricing. Together with Lemma 3 it yields a floor for the smallest eigenvalue along the whole run.
--
--   **Formalization Note** The lemma's existential "there exists a sufficiently small $k=k(d)$" is implied by the explicit choice $k=1/(400d^2)$ stated here. The hypothesis $\|x\|\le1$ is not written in the lemma; it is the standing normalization of §3 (p. 7) and the proof uses it ($\sum_ic_i^2\le1$, p. 19). It is encoded as $x\cdot x\le1$. The paper's "the lemma trivially holds for $d=1$" refers to a case in which (4) is undefined, so $d\ge2$.
-- source:
--   Cohen, Lobel, Paes Leme, Feature-Based Dynamic Pricing, Management Science (2020), DOI 10.1287/mnsc.2019.3485 (authors' copy, SSRN 2737045), p. 18, Lemma 4 (proof pp. 18–19)

import Mathlib
import Definitions.Def_FeaturePricing_Ellipsoid_MinEigenvalue
import Definitions.Def_LinearOptimization_EllipsoidMethod

namespace FeaturePricing.Ellipsoid

open Matrix LinearOptimization

/-- **Lemma 4, p. 18**, with `k = 1/(400d²)`. For `d ≥ 2`, `ε > 0`, `A` positive definite and a
feature vector with `‖x‖ ≤ 1` (Euclidean, the normalization of §3): if `λ_d(A) ≤ kε²` and
`x′Ax > ε²/4`, then the matrix `Ã` of Eq. (4) satisfies `λ_d(Ã) ≥ λ_d(A)`. -/
theorem lemma4_min_eigenvalue_no_decrease {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (x : Fin d → ℝ) (hx : x ⬝ᵥ x ≤ 1)
    (hsmall : lamMin A ≤ 1 / (400 * (d : ℝ) ^ 2) * ε ^ 2)
    (hexplore : ε ^ 2 / 4 < x ⬝ᵥ A *ᵥ x) :
    lamMin A ≤ lamMin (ellipsoidUpdateMatrix A x) := by sorry

end FeaturePricing.Ellipsoid
