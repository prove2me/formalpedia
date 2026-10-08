-- Prove2me | Theorems.Thm_FeaturePricing_Ellipsoid_lemma3_min_eigenvalue_shrink
-- name    : FeaturePricing.Ellipsoid.lemma3_min_eigenvalue_shrink
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:33:53.039079+00:00
-- url     : https://prove2.me/theorems/141bb0c2-86e9-4e70-94ef-357cfed246b2
-- title:
--   Lemma 3, p. 17 — an explore step shrinks λ_d by at most d²/(d+1)²
-- statement:
--   Let $d\ge2$, let $A$ be a positive definite $d\times d$ matrix and $x\in\mathbb R^d\setminus\{0\}$, and let $\tilde A=\frac{d^2}{d^2-1}\big(A-\frac{2}{d+1}bb'\big)$ with $b=Ax/\sqrt{x'Ax}$ be the update (4). Then
--   $$
--   \lambda_d(\tilde A)\ \ge\ \frac{d^2}{(d+1)^2}\,\lambda_d(A).
--   $$
--
--   In EllipsoidPricing, $A_{t+1}=\tilde A$ (with $A=A_t$, $x=x_t$) at every exploration step $t$, whether or not a sale occurs, so this is the paper's "for any exploration step $t$, $\lambda_d(A_{t+1})\ge\frac{d^2}{(d+1)^2}\lambda_d(A_t)$". It limits how fast the smallest eigenvalue can shrink.
--
--   **Formalization Note** Stated for the matrix update rather than along a run: every exploration step has $A_t\succ0$ and $x_t\ne0$ (because $x_t'A_tx_t>\epsilon^2/4>0$), so this form implies the paper's. $\tilde A$ is `ellipsoidUpdateMatrix A x`; $\lambda_d$ is `lamMin`.
-- source:
--   Cohen, Lobel, Paes Leme, Feature-Based Dynamic Pricing, Management Science (2020), DOI 10.1287/mnsc.2019.3485 (authors' copy, SSRN 2737045), p. 17, Lemma 3

import Mathlib
import Definitions.Def_FeaturePricing_Ellipsoid_MinEigenvalue
import Definitions.Def_LinearOptimization_EllipsoidMethod

namespace FeaturePricing.Ellipsoid

open Matrix LinearOptimization

/-- **Lemma 3, p. 17.** In an exploration step the smallest eigenvalue shrinks by at most the
factor `d²/(d+1)²`: for `d ≥ 2`, `A` positive definite and `x ≠ 0`, the matrix `Ã` of Eq. (4)
satisfies `λ_d(Ã) ≥ (d²/(d+1)²) λ_d(A)`. -/
theorem lemma3_min_eigenvalue_shrink {d : ℕ} (hd : 2 ≤ d) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (x : Fin d → ℝ) (hx : x ≠ 0) :
    (d : ℝ) ^ 2 / ((d : ℝ) + 1) ^ 2 * lamMin A ≤ lamMin (ellipsoidUpdateMatrix A x) := by sorry

end FeaturePricing.Ellipsoid
