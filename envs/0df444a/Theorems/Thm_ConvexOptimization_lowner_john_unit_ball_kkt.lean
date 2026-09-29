-- Prove2me | Theorems.Thm_ConvexOptimization_lowner_john_unit_ball_kkt
-- name    : ConvexOptimization.lowner_john_unit_ball_kkt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T04:10:53.943617+00:00
-- url     : https://prove2.me/theorems/586e2914-1cc4-4335-9c07-1471479d80ef
-- title:
--   KKT identities at the normalized optimum
-- statement:
--   The optimality (KKT) conditions of the minimum-volume covering ellipsoid problem, written at the normalized optimum where the extremal ellipsoid is the Euclidean unit ball.
--
--   Let $x_1,\dots,x_m \in \mathbb{R}^n$ and suppose the pair $(A,b) = (I,0)$ — that is, the closed unit ball $\{v : \lVert v\rVert_2 \le 1\}$ — is the Löwner–John ellipsoid of $\{x_1,\dots,x_m\}$. Then there exist multipliers $\lambda_1,\dots,\lambda_m \ge 0$ with
--
--   $$\sum_{i=1}^{m} \lambda_i\, x_i x_i^{T} = I, \qquad \sum_{i=1}^{m} \lambda_i\, x_i = 0, \qquad \lambda_i\bigl(1 - x_i^{T}x_i\bigr) = 0 \quad (i = 1,\dots,m), \qquad \sum_{i=1}^{m} \lambda_i = n .$$
--
--   Here $x_i x_i^{T}$ denotes the rank-one outer product, $I$ the $n \times n$ identity, and $n$ the dimension. The first identity is stationarity of the $\log\det$ objective, the second stationarity in the centre variable, the third is complementary slackness — a multiplier may be nonzero only at a *contact point*, one with $\lVert x_i\rVert_2 = 1$ lying on the boundary sphere — and the last is the trace of the first combined with complementary slackness.
--
--   These are exactly John's decomposition of the identity: the contact points, weighted by $\lambda$, form an isotropic system whose second-moment matrix is the identity and whose barycentre is the origin. Because the Löwner–John ellipsoid is affinely equivariant, every configuration can be brought to this normalized position, so these identities are the general optimality conditions written in the coordinates that make them cleanest. They are the sole input to the $1/n$ rounding step.
--
--   **Formalization Note** The outer product is Mathlib's `Matrix.vecMulVec`, and $x_i^{T}x_i$ is written with the dot product `⬝ᵥ` on `Fin n → ℝ`; the identity matrix appears as `(1 : Matrix (Fin n) (Fin n) ℝ)`. No full-dimensionality hypothesis is required, since it follows from the unit ball being extremal. Source: Boyd & Vandenberghe §8.4.1, the KKT conditions of problem (8.12) after normalization.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 412, §8.4.1 (the KKT conditions of problem (8.12), written at the normalized optimum where the extremal ellipsoid is the Euclidean unit ball)

import Mathlib
import Definitions.Def_ConvexOptimization_ellipsoidBody
import Definitions.Def_ConvexOptimization_IsLownerJohn

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.lowner_john_unit_ball_kkt {nn m : ℕ} (x : Fin m → Fin nn → ℝ)
    (hopt : IsLownerJohn (1 : Matrix (Fin nn) (Fin nn) ℝ) 0 (Set.range x)) :
    ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧
      (∑ i, lam i • Matrix.vecMulVec (x i) (x i)) = (1 : Matrix (Fin nn) (Fin nn) ℝ) ∧
      (∑ i, lam i • x i) = 0 ∧
      (∀ i, lam i * (1 - x i ⬝ᵥ x i) = 0) ∧
      (∑ i, lam i) = (nn : ℝ) := by
  sorry
