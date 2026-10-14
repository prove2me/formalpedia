-- Prove2me | Theorems.Thm_BenchmarkTracking_Verification_theorem_4_1
-- name    : BenchmarkTracking.Verification.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:19.262386+00:00
-- url     : https://prove2.me/theorems/8e05c50f-e333-4b1b-b528-bd5f82984861
-- title:
--   Theorem 4.1 — verification theorem: $u$ solves the HJB equation, is the value function, and the feedback $(\theta^*,c^*)$ is optimal
-- statement:
--   Let the model parameters satisfy the standing assumptions, with $\mu_Z>\kappa_2$ and $\sigma_B\neq0$. There is $\rho_0>0$, depending only on the model parameters, such that for every discount rate $\rho>\rho_0$ the following holds, with $u$ the function
--   $$
--   u(x,h,z)=\inf_{y\in(0,\beta]}\{\hat u(y,h,z)+yx\},\qquad \hat u(y,h,z)=v\Big(-\ln\frac y\beta,h,z\Big),
--   $$
--   built from the probabilistic representation $v$ of (3.1) on any probability space carrying three independent standard Brownian motions.
--
--   1. **(i)** For every $(x,h,z)\in\mathbb R^3_+$ the infimum is attained; $u$ is a classical solution of the HJB equation (4.2) with $u_x(0,h,z)=\beta$ and $u_h(x,0,z)=u_x(x,0,z)$; and $u_x>0$, $u_{xx}<0$ on $\mathbb R^3_+$.
--   2. **(ii) Verification inequality.** On every filtered probability space satisfying the usual conditions and carrying a $d$-dimensional Brownian motion, for every admissible strategy $(\theta,c)\in\mathbb U^r$ and every $(x,h,z)\in\mathbb R^3_+$,
--   $$
--   \mathbb E\Big[\int_0^\infty e^{-\rho t}\frac{c_t^p}p\,dt\Big]\le u(x,h,z)+\beta\,\mathbb E\Big[\int_0^\infty e^{-\rho t}dL^X_t\Big].
--   $$
--   3. **(ii) Optimality.** For every $(x,h,z)\in\mathbb R^3_+$ the controlled reflected system (4.4) has a solution $(X^*,I,Z)$ on some such space along which the feedback strategy $\theta^*_t=\theta^*(X^*_t,I_t,Z_t)$, $c^*_t=c^*(X^*_t,I_t,Z_t)$ of (4.3) is admissible, the expected discounted capital injection $\mathbb E[\int_0^\infty e^{-\rho t}dL^{X^*}_t]$ is finite, and equality holds in the inequality above.
--
--   Thus $u$ is the value function (2.5) of the auxiliary problem, and the feedback strategy is optimal.
--
--   **Formalization Note** The theorem's $\rho_0$ is "specified later in (4.45)", but that formula depends on $\rho$ itself (through $C_2$ and $\hat\mu=\alpha/2-\rho/\alpha$) and on a symbol $\kappa$ not defined in the paper, so the threshold is stated existentially, after all model parameters and before $\rho$. The hypotheses $\mu_Z>\kappa_2$ and $\sigma_B\neq0$ are not printed in Theorem 4.1; its proof of (i) rests on Theorem 3.1, Lemma 3.2 and Lemma 3.4, which assume them. The objective is written as "utility $\le u+\beta\cdot$cost" in the extended reals, which equals the paper's $J\le u$ whenever $J$ is defined and never meets $\infty-\infty$. The optimal pair is asserted to exist on a weak solution of (4.4); the paper cites Łaukajtys–Słomiński for existence. The conclusions $u_x>0$, $u_{xx}<0$, attainment of the infimum and finiteness of the optimal cost are established in the paper's proof and make the feedback and the objective well defined.
-- source:
--   Bo, Huang & Yu, Stochastic control problems with state-reflections arising from relaxed benchmark tracking, arXiv:2302.08302v4, pp. 18–19, Theorem 4.1 (4.1)–(4.4)

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_BenchmarkTracking_Verification_Model
import Definitions.Def_BenchmarkTracking_Verification_Analysis
import Definitions.Def_BenchmarkTracking_Verification_Representation
import Definitions.Def_BenchmarkTracking_Verification_PDE
import Definitions.Def_BenchmarkTracking_Verification_Control

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BenchmarkTracking.Verification

theorem theorem_4_1 {d : ℕ} (M : Params d) (hM : M.Standing) (hZ : M.kappa2 < M.muZ)
    (hσB : M.sigmaB ≠ 0) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ < ρ →
      ∀ (Ω₀ : Type) [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
        (B : ℝ≥0 → Ω₀ → EuclideanSpace ℝ (Fin 3)), EthierKurtz.IsStandardBrownian P₀ B →
      -- (i) `u` of (4.1) is a classical solution of (4.2); the infimum is attained;
      -- `u_x > 0` and `u_xx < 0` (so the feedback (4.3) is well defined)
      ((∀ x h z : ℝ, 0 ≤ x → 0 ≤ h → 0 ≤ z →
          ∃ y ∈ Ioc 0 M.beta, ∀ y' ∈ Ioc 0 M.beta,
            uHat M ρ P₀ B y h z + y * x ≤ uHat M ρ P₀ B y' h z + y' * x) ∧
        IsClassicalSolHJB M ρ (uPrimal M ρ P₀ B) ∧
        ∀ x h z : ℝ, 0 ≤ x → 0 ≤ h → 0 ≤ z →
          0 < pd3₁ (uPrimal M ρ P₀ B) (Ici 0) x h z ∧
            pd3₁ (pd3₁ (uPrimal M ρ P₀ B) (Ici 0)) (Ici 0) x h z < 0) ∧
      -- (ii) verification inequality: `J(x, h, z; θ, c) ≤ u(x, h, z)` for every `(θ, c) ∈ 𝕌^r`
      (∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (Pr : Measure Ω) (F : Filtration ℝ≥0 mΩ)
          (W : Ω → ℝ → Fin d → ℝ), IsControlBasis Pr F W →
        ∀ (θ : ℝ≥0 → Ω → (Fin d → ℝ)) (c : ℝ≥0 → Ω → ℝ) (J : Fin d → ℝ≥0 → Ω → ℝ),
          IsAdmissible M Pr F W θ c J →
          ∀ x h z : ℝ, 0 ≤ x → 0 ≤ h → 0 ≤ z →
            utilityTerm M ρ Pr c ≤
              (uPrimal M ρ P₀ B x h z : EReal) +
                (M.beta : EReal) * (costTerm M ρ Pr W θ c J x h z : EReal)) ∧
      -- (ii) optimality: (4.4) has a solution along which `(θ*, c*) ∈ 𝕌^r` attains `u`
      (∀ x h z : ℝ, 0 ≤ x → 0 ≤ h → 0 ≤ z →
        ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (Pr : Measure Ω) (F : Filtration ℝ≥0 mΩ)
          (W : Ω → ℝ → Fin d → ℝ) (X : ℝ≥0 → Ω → ℝ) (J : Fin d → ℝ≥0 → Ω → ℝ),
          IsControlBasis Pr F W ∧
          IsFeedbackSolution M Pr F W (uPrimal M ρ P₀ B) x h z X J ∧
          costTerm M ρ Pr W (thetaProc M W (uPrimal M ρ P₀ B) h z X)
              (cProc M W (uPrimal M ρ P₀ B) h z X) J x h z < ∞ ∧
          utilityTerm M ρ Pr (cProc M W (uPrimal M ρ P₀ B) h z X) =
            (uPrimal M ρ P₀ B x h z : EReal) +
              (M.beta : EReal) *
                (costTerm M ρ Pr W (thetaProc M W (uPrimal M ρ P₀ B) h z X)
                  (cProc M W (uPrimal M ρ P₀ B) h z X) J x h z : EReal)) := by sorry

end BenchmarkTracking.Verification
