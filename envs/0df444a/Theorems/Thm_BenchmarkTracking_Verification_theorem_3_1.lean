-- Prove2me | Theorems.Thm_BenchmarkTracking_Verification_theorem_3_1
-- name    : BenchmarkTracking.Verification.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:31.219888+00:00
-- url     : https://prove2.me/theorems/625f8f5b-d5ba-47b4-ba92-67e93ce5d4f9
-- title:
--   Theorem 3.1 — $\hat u$ is strictly convex in $y$ and solves the dual Neumann problem (2.8), (2.10), (2.11)
-- statement:
--   Let the model parameters satisfy the standing assumptions, $\rho>0$, and
--   $$
--   \rho>\frac{\alpha^2p}{2(1-p)},\qquad \mu_Z>\kappa_2,\qquad \rho>\frac{\alpha^2|p|}{2(1-p)}+\mu_Z,\qquad \sigma_B\neq0 .
--   $$
--   On any probability space carrying three independent standard Brownian motions, let $v$ be the representation (3.1) and $\hat u(y,h,z)=v(-\ln(y/\beta),h,z)$ for $(y,h,z)\in(0,\beta]\times\mathbb R^2_+$. Then:
--
--   1. the three expectations in (3.1) are finite for every $(r,h,z)\in\mathbb R^3_+$;
--   2. for each $(h,z)\in\mathbb R^2_+$ the function $(0,\beta]\ni y\mapsto\hat u(y,h,z)$ is strictly convex;
--   3. $\hat u$ is a classical solution of the dual PDE (2.8) with the Neumann conditions $\hat u_y(\beta,h,z)=0$ (2.10) and $\hat u_h(y,0,z)=y$ (2.11).
--
--   This is the solvability result for the dual problem; its Legendre-type inverse is the value function in Theorem 4.1.
--
--   **Formalization Note** The theorem prints only $\rho>\alpha^2p/(2(1-p))$ and $\mu_Z>\kappa_2$. Its proof applies Lemma 3.2, which assumes $\rho>\alpha^2|p|/(2(1-p))+\mu_Z$, and Lemma 3.4, which assumes $\sigma_B\neq0$; both are added. The paper prints (2.11) as $\hat u_z(y,0,z)=y$; the condition is on $\hat u_h$. The uniqueness sentence "On the other hand, …" is not part of this statement.
-- source:
--   Bo, Huang & Yu, Stochastic control problems with state-reflections arising from relaxed benchmark tracking, arXiv:2302.08302v4, pp. 8–9, Theorem 3.1; p. 7 (2.8)–(2.11)

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_BenchmarkTracking_Verification_Model
import Definitions.Def_BenchmarkTracking_Verification_Analysis
import Definitions.Def_BenchmarkTracking_Verification_Representation
import Definitions.Def_BenchmarkTracking_Verification_PDE

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BenchmarkTracking.Verification

theorem theorem_3_1 {d : ℕ} (M : Params d) (hM : M.Standing) (ρ : ℝ) (hρ0 : 0 < ρ)
    (hρp : M.alpha ^ 2 * M.p / (2 * (1 - M.p)) < ρ) (hZ : M.kappa2 < M.muZ)
    (hρ : M.alpha ^ 2 * |M.p| / (2 * (1 - M.p)) + M.muZ < ρ) (hσB : M.sigmaB ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (hB : EthierKurtz.IsStandardBrownian Pr B) :
    (∀ r h z : ℝ, 0 ≤ r → 0 ≤ h → 0 ≤ z →
      expect1 M ρ Pr B r < ∞ ∧ expect2 M ρ Pr B r z < ∞ ∧ expect3 M ρ Pr B r h < ∞) ∧
    (∀ h z : ℝ, 0 ≤ h → 0 ≤ z →
      StrictConvexOn ℝ (Ioc 0 M.beta) (fun y => uHat M ρ Pr B y h z)) ∧
    IsClassicalSolDual M ρ (uHat M ρ Pr B) := by sorry

end BenchmarkTracking.Verification
