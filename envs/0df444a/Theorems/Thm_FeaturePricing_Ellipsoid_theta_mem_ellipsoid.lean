-- Prove2me | Theorems.Thm_FeaturePricing_Ellipsoid_theta_mem_ellipsoid
-- name    : FeaturePricing.Ellipsoid.theta_mem_ellipsoid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:32:13.46129+00:00
-- url     : https://prove2.me/theorems/c3ada608-b493-4ee4-a65b-2d810943c663
-- title:
--   §5, p. 11 (construction) — θ ∈ E_t and A_t ≻ 0 for every t
-- statement:
--   Run EllipsoidPricing in dimension $d\ge2$ with parameter $\epsilon>0$ from $E_1=B(0,R)$, $R>0$, on any feature sequence $(x_t)$, with true parameter $\theta$ satisfying $\|\theta\|\le R$ (Euclidean norm). Then for every period $t$
--   $$
--   A_t\succ0\qquad\text{and}\qquad \theta\in E_t=E(A_t,a_t).
--   $$
--
--   The paper uses this fact without a separate statement: every update keeps the half-ellipsoid $H_{t+1}$, which contains $\theta$ because the sale/no-sale feedback is consistent with $\theta$, inside $E_{t+1}$. It is what makes $[\underline b_t,\bar b_t]$ an interval containing the market value $\theta'x_t$, and positive definiteness makes Lemmas 3–4 applicable along the run.
--
--   **Formalization Note** Lean period $t$ is the paper's period $t+1$. $\|\theta\|\le R$ is encoded as $\theta\cdot\theta\le R^2$.
-- source:
--   Cohen, Lobel, Paes Leme, Feature-Based Dynamic Pricing, Management Science (2020), DOI 10.1287/mnsc.2019.3485 (authors' copy, SSRN 2737045), p. 11, §5 (construction of E_{t+1} ⊇ H_{t+1}); used in the proof of Theorem 2, p. 15

import Mathlib
import Definitions.Def_FeaturePricing_Ellipsoid_EllipsoidPricing

namespace FeaturePricing.Ellipsoid

open Matrix LinearOptimization

/-- **§5, p. 11 (construction).** Along every run of EllipsoidPricing started from
`E₁ = B(0, R)`, every shape matrix `A_t` is positive definite and the true parameter `θ`
(with `‖θ‖ ≤ R`, Euclidean) lies in every ellipsoid `E_t = E(A_t, a_t)`. Lean period `t` is the
paper's period `t + 1`. -/
theorem theta_mem_ellipsoid {d : ℕ} (hd : 2 ≤ d) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (θ : Fin d → ℝ) (hθ : θ ⬝ᵥ θ ≤ R ^ 2) (x : ℕ → Fin d → ℝ) (t : ℕ) :
    (shape R ε θ x t).PosDef ∧ θ ∈ ellipsoid (center R ε θ x t) (shape R ε θ x t) := by sorry

end FeaturePricing.Ellipsoid
