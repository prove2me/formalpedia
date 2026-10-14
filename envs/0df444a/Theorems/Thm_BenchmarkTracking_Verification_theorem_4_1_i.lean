-- Prove2me | Theorems.Thm_BenchmarkTracking_Verification_theorem_4_1_i
-- name    : BenchmarkTracking.Verification.theorem_4_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:24.87603+00:00
-- url     : https://prove2.me/theorems/cadd2d5d-6f6c-4702-bae3-82141ae9fbc1
-- title:
--   Theorem 4.1(i) — $u=\inf_y\{\hat u+yx\}$ is a classical solution of the HJB equation (4.2)
-- statement:
--   Let the model parameters satisfy the standing assumptions, $\rho>0$, $\rho>\frac{\alpha^2p}{2(1-p)}$, $\mu_Z>\kappa_2$, $\rho>\frac{\alpha^2|p|}{2(1-p)}+\mu_Z$ and $\sigma_B\neq0$. On any probability space carrying three independent standard Brownian motions, let $\hat u(y,h,z)=v(-\ln(y/\beta),h,z)$ with $v$ of (3.1), and
--   $$
--   u(x,h,z)=\inf_{y\in(0,\beta]}\{\hat u(y,h,z)+yx\},\qquad (x,h,z)\in\mathbb R^3_+ .
--   $$
--   Then:
--
--   1. for every $(x,h,z)\in\mathbb R^3_+$ the infimum is attained at some $y^*\in(0,\beta]$;
--   2. $u$ is a classical solution of the HJB equation (4.2) with the Neumann conditions $u_x(0,h,z)=\beta$ and $u_h(x,0,z)=u_x(x,0,z)$;
--   3. $u_x>0$ and $u_{xx}<0$ on $\mathbb R^3_+$.
--
--   This is the first half of the verification theorem: the dual solution yields a classical solution of the primal HJB equation.
--
--   **Formalization Note** The theorem is stated under the hypotheses its proof uses (those of Theorem 3.1 as formalized here, which include Lemma 3.2's and Lemma 3.4's) rather than under the unspecified "$\rho>\rho_0$" of Theorem 4.1; any admissible $\rho_0$ of (4.45) exceeds these thresholds. Conclusion 3 is the property "$u_{xx}<0$ and $u_x\ge0$" that p. 7 announces "will be verified in later sections"; the proof of (i) gives $u_x=y^*\in(0,\beta]$ and strict concavity in $x$, and it makes the feedback (4.3) well defined. Conclusion 1 makes the real infimum in (4.1) a genuine minimum.
-- source:
--   Bo, Huang & Yu, Stochastic control problems with state-reflections arising from relaxed benchmark tracking, arXiv:2302.08302v4, pp. 18–19, Theorem 4.1(i) (4.1)–(4.2); proof pp. 19–20

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_BenchmarkTracking_Verification_Model
import Definitions.Def_BenchmarkTracking_Verification_Analysis
import Definitions.Def_BenchmarkTracking_Verification_Representation
import Definitions.Def_BenchmarkTracking_Verification_PDE

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BenchmarkTracking.Verification

theorem theorem_4_1_i {d : ℕ} (M : Params d) (hM : M.Standing) (ρ : ℝ) (hρ0 : 0 < ρ)
    (hρp : M.alpha ^ 2 * M.p / (2 * (1 - M.p)) < ρ)
    (hZ : M.kappa2 < M.muZ) (hρ : M.alpha ^ 2 * |M.p| / (2 * (1 - M.p)) + M.muZ < ρ)
    (hσB : M.sigmaB ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (hB : EthierKurtz.IsStandardBrownian Pr B) :
    (∀ x h z : ℝ, 0 ≤ x → 0 ≤ h → 0 ≤ z →
      ∃ y ∈ Ioc 0 M.beta, ∀ y' ∈ Ioc 0 M.beta,
        uHat M ρ Pr B y h z + y * x ≤ uHat M ρ Pr B y' h z + y' * x) ∧
    IsClassicalSolHJB M ρ (uPrimal M ρ Pr B) ∧
    ∀ x h z : ℝ, 0 ≤ x → 0 ≤ h → 0 ≤ z →
      0 < pd3₁ (uPrimal M ρ Pr B) (Ici 0) x h z ∧
        pd3₁ (pd3₁ (uPrimal M ρ Pr B) (Ici 0)) (Ici 0) x h z < 0 := by sorry

end BenchmarkTracking.Verification
