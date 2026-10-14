-- Prove2me | Theorems.Thm_DynPrincipalAgent_HJB_lemma_2_5
-- name    : DynPrincipalAgent.HJB.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:33:19.6755+00:00
-- url     : https://prove2.me/theorems/35d7ec40-82bd-4bd8-a5b6-8a07fd0ace4b
-- title:
--   Lemma 2.5, (2.20), p. 10 — a priori estimates for admissible contracts
-- statement:
--   Let Assumption 2.2 hold. There is a constant $C>0$, depending only on $T$, $C_0$ and $\Lambda_0$, such that for every type $\theta$, every $t<T$, every $x\le\overline L^\theta_t$ and every $(\eta,Z)\in\mathcal A^\theta_{t,x}$,
--   $$\mathbb E^{\theta,Z}\Big[\int_t^T\big[|Z_s|^2+C_0-\eta_s\big]ds\Big]\le C\big[\overline L^\theta_t-x\big],\qquad \mathbb E^{\theta,Z}\Big[\int_t^T|\eta_s|^2ds\Big]\le C\big[T-t-x\big].$$
--   Here $\mathbb E^{\theta,Z}$ is the expectation under the Girsanov measure of the agent's optimal effort $I^h(\theta;\cdot,Z)$.
--
--   These estimates bound the principal's payoff from any admissible contract, and are used throughout the paper.
--
--   **Formalization Note.** Only the consequence (2.20) is stated; the conditional estimate (2.19) on the BSDE solution is not. The constant is chosen before the model, uniformly over all type sets, models, probability spaces, types and controls. Both expectations are lower integrals in $[0,\infty]$ of nonnegative integrands, so no integrability is presupposed.
-- source:
--   Zhang & Zhu, A Dynamic Principal Agent Problem with One-sided Commitment, arXiv:2208.06473v3, Lemma 2.5, (2.20), p. 10

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_DynPrincipalAgent_HJB_Model
import Definitions.Def_DynPrincipalAgent_HJB_Viscosity
import Definitions.Def_DynPrincipalAgent_HJB_Controls
import Definitions.Def_DynPrincipalAgent_HJB_Quitting

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Peng1990.SMP

namespace DynPrincipalAgent.HJB

theorem lemma_2_5 : ∀ (T : ℝ≥0) (C₀ Λ₀ : ℝ), ∃ C : ℝ, 0 < C ∧
    ∀ {Θ : Type} [MeasurableSpace Θ] (M : Model Θ), M.T = T → M.C₀ = C₀ → M.Λ₀ = Λ₀ → M.A22 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (θ : Θ) (t : ℝ≥0) (x : ℝ),
      t < M.T → x ≤ M.Lbar θ t →
      ∀ η Z : ℝ≥0 → Ω → ℝ, M.InA S θ t x η Z →
      ∀ I : ℝ≥0 → Ω → ℝ,
        IsItoIntegral (S.filt t) S.P M.T S.B (startAt t (M.alpha (fun _ _ => θ) Z)) I →
        (∫⁻ ω, ∫⁻ r in Icc (t : ℝ) M.T,
            ENNReal.ofReal ((Z r.toNNReal ω) ^ 2 + M.C₀ - η r.toNNReal ω)
            ∂volume ∂(M.girsanov S t (M.alpha (fun _ _ => θ) Z) I)
          ≤ ENNReal.ofReal (C * (M.Lbar θ t - x))) ∧
        (∫⁻ ω, ∫⁻ r in Icc (t : ℝ) M.T, ENNReal.ofReal ((η r.toNNReal ω) ^ 2)
            ∂volume ∂(M.girsanov S t (M.alpha (fun _ _ => θ) Z) I)
          ≤ ENNReal.ofReal (C * ((M.T : ℝ) - t - x))) := by sorry

end DynPrincipalAgent.HJB
