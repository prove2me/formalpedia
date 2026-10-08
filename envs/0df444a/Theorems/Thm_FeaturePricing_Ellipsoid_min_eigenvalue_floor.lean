-- Prove2me | Theorems.Thm_FeaturePricing_Ellipsoid_min_eigenvalue_floor
-- name    : FeaturePricing.Ellipsoid.min_eigenvalue_floor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:33:18.190511+00:00
-- url     : https://prove2.me/theorems/1e77940d-c68d-4606-aed9-1672d4763d86
-- title:
--   Proof of Lemma 1, p. 20 — λ_d(A_t) ≥ ε²/(400(d+1)²) at every period
-- statement:
--   Run EllipsoidPricing in dimension $d\ge2$ from $E_1=B(0,R)$, $R>0$, with parameter $0<\epsilon\le20R(d+1)$, on a feature sequence with $\|x_t\|\le1$ for all $t$, and true parameter $\|\theta\|\le R$ (Euclidean norms). Then for every period $t$,
--   $$
--   \lambda_d(A_t)\ \ge\ \frac{d^2}{(d+1)^2}\cdot\frac{\epsilon^2}{400d^2}=\frac{\epsilon^2}{400(d+1)^2}.
--   $$
--
--   This is the eigenvalue floor of the proof of Lemma 1: by Lemma 4 the smallest eigenvalue cannot shrink once it is below $\epsilon^2/400d^2$, and by Lemma 3 a single shrinking step loses at most the factor $d^2/(d+1)^2$. With the volume formula it gives the lower bound on the volume of the ellipsoid that is compared with the volume decrease.
--
--   **Formalization Note** The paper states the floor for $\tilde A_{n+1}$, the shape after the $n$-th exploration step; shapes do not change in exploitation periods, so "every period $t$" is the same statement. The hypothesis $\epsilon\le20R(d+1)$ is not printed: it is equivalent to the initial floor $\lambda_d(A_1)=R^2\ge\epsilon^2/(400(d+1)^2)$, which the argument needs at time 1 (for larger $\epsilon$ the stated floor exceeds $R^2$ and fails at $t=1$). Lean period $t$ is the paper's $t+1$.
-- source:
--   Cohen, Lobel, Paes Leme, Feature-Based Dynamic Pricing, Management Science (2020), DOI 10.1287/mnsc.2019.3485 (authors' copy, SSRN 2737045), p. 20, proof of Lemma 1, first display

import Mathlib
import Definitions.Def_FeaturePricing_Ellipsoid_MinEigenvalue
import Definitions.Def_FeaturePricing_Ellipsoid_EllipsoidPricing

namespace FeaturePricing.Ellipsoid

open Matrix LinearOptimization

/-- **Proof of Lemma 1, p. 20.** Along every run of EllipsoidPricing from `E₁ = B(0, R)` with
`0 < ε ≤ 20R(d+1)` and features `‖x_t‖ ≤ 1` (Euclidean), the smallest eigenvalue of every shape
matrix satisfies `λ_d(A_t) ≥ ε²/(400(d+1)²)`. -/
theorem min_eigenvalue_floor {d : ℕ} (hd : 2 ≤ d) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hεR : ε ≤ 20 * R * ((d : ℝ) + 1))
    (θ : Fin d → ℝ) (hθ : θ ⬝ᵥ θ ≤ R ^ 2) (x : ℕ → Fin d → ℝ) (hx : ∀ t, x t ⬝ᵥ x t ≤ 1)
    (t : ℕ) :
    ε ^ 2 / (400 * ((d : ℝ) + 1) ^ 2) ≤ lamMin (shape R ε θ x t) := by sorry

end FeaturePricing.Ellipsoid
