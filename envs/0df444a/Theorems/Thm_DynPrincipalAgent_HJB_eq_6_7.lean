-- Prove2me | Theorems.Thm_DynPrincipalAgent_HJB_eq_6_7
-- name    : DynPrincipalAgent.HJB.eq_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:34:10.437085+00:00
-- url     : https://prove2.me/theorems/86d458fb-0aa1-444c-9a1e-5faa642de370
-- title:
--   (6.7), proof of Theorem 6.3, p. 31 — the dynamic programming principle for u_∞
-- statement:
--   Let Assumptions 2.2 and 3.1 hold. For every type $\theta$, every $(t,x)\in D_\theta$ and every $\mathbb F^t$-stopping time $\tau$ with values in $[t,T]$, writing $\sigma=\tau^{\theta;t,x,\eta,Z}$ for the quitting time of the current agent,
--   $$u_\infty(\theta;t,x)=\sup_{(\eta,Z)\in\mathcal A^\theta_{t,x}}\mathbb E^{\theta,Z}\Big[\int_t^{\tau\wedge\sigma}\big[I^h(\theta;r,Z_r)-\eta_r\big]dr+u_\infty\big(\theta;\tau,\mathcal X^{\theta;t,x,\eta,Z}_\tau\big)\mathbf 1_{\{\tau<\sigma\}}+\overline u_\infty(\sigma)\mathbf 1_{\{\sigma\le\tau,\ \sigma<T\}}\Big].$$
--
--   Before the current agent quits the principal continues with the same value function; at the quitting time she hires the best new agent and pays $c^P$, which is the value $\overline u_\infty$.
--
--   **Formalization Note.** The paper writes "$u_\infty(\theta;t,x):=$", but (6.7) is an identity, not a definition. The supremum is stated with `IsLUB`. The expectation is recorded only when it is genuine (integrable payoff, almost surely integrable running reward).
-- source:
--   Zhang & Zhu, A Dynamic Principal Agent Problem with One-sided Commitment, arXiv:2208.06473v3, proof of Theorem 6.3, (6.7), pp. 31–32

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

theorem eq_6_7 {Θ : Type} [MeasurableSpace Θ] (M : Model Θ) (hM : M.Standing)
    {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (θ : Θ) (t : ℝ≥0) (x : ℝ)
    (hD : ((t : ℝ), x) ∈ M.D θ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (S.filt t) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, t ≤ τ ω ∧ τ ω ≤ M.T) :
    IsLUB {v : ℝ | ∃ (η Z J I : ℝ≥0 → Ω → ℝ),
        M.InAWith S θ t x η Z J ∧
        IsItoIntegral (S.filt t) S.P M.T S.B (startAt t (M.alpha (fun _ _ => θ) Z)) I ∧
        (∀ᵐ ω ∂S.P, IntegrableOn (fun r : ℝ => M.Ih θ r (Z r.toNNReal ω) - η r.toNNReal ω)
          (Icc (t : ℝ) M.T)) ∧
        Integrable (fun ω =>
            (∫ r in Icc (t : ℝ) (min (τ ω) (M.hitTime θ t x η Z J ω)),
              (M.Ih θ r (Z r.toNNReal ω) - η r.toNNReal ω))
            + (if τ ω < M.hitTime θ t x η Z J ω then
                M.uInf S θ (τ ω) (M.fwd θ t x η Z J (τ ω) ω) else 0)
            + (if M.hitTime θ t x η Z J ω ≤ τ ω ∧ M.hitTime θ t x η Z J ω < M.T then
                M.uInfBar S (M.hitTime θ t x η Z J ω) else 0))
          (M.girsanov S t (M.alpha (fun _ _ => θ) Z) I) ∧
        v = ∫ ω,
            ((∫ r in Icc (t : ℝ) (min (τ ω) (M.hitTime θ t x η Z J ω)),
              (M.Ih θ r (Z r.toNNReal ω) - η r.toNNReal ω))
            + (if τ ω < M.hitTime θ t x η Z J ω then
                M.uInf S θ (τ ω) (M.fwd θ t x η Z J (τ ω) ω) else 0)
            + (if M.hitTime θ t x η Z J ω ≤ τ ω ∧ M.hitTime θ t x η Z J ω < M.T then
                M.uInfBar S (M.hitTime θ t x η Z J ω) else 0))
            ∂(M.girsanov S t (M.alpha (fun _ _ => θ) Z) I)}
      (M.uInf S θ t x) := by sorry

end DynPrincipalAgent.HJB
