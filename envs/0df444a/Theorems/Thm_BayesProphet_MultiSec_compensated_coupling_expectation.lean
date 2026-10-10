-- Prove2me | Theorems.Thm_BayesProphet_MultiSec_compensated_coupling_expectation
-- name    : BayesProphet.MultiSec.compensated_coupling_expectation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:45:59.124181+00:00
-- url     : https://prove2.me/theorems/8f31e412-5b46-4d39-93fe-98e3b0a9df6f
-- title:
--   Lemma 1 (Compensated Coupling) — expected regret bound
-- statement:
--   Let an online decision problem satisfy the standing assumption, let $\pi^{\mathrm{on}}$ be an online policy for horizon $T$ started in $s_0$, and let the arrival sequence $\theta[\omega]$ be random on a probability space $(\Omega,\mathcal F,\mathbb P)$, with integrable regret. If $C$ bounds every marginal compensation of a feasible action, $\partial R(t,a,s)[\omega]\le C$ for all $t\in[T]$, states $s$, feasible $a$ and $\omega\in\Omega$ (the smallest such $C$ is $\max_{a,j}\partial r(a,j)$), then
--   $$\mathbb E[\mathrm{Reg}]\le C\cdot\sum_{t\in[T]}\mathbb P\big[Q(t,S^t)\big].$$
--
--   This is the expectation form of the compensated coupling: the expected regret is at most the largest compensation times the expected number of disagreements.
--
--   **Formalization Note** The paper writes $\sum_t\mathbb E[\mathbb P[Q(t,S^t)\mid S^t]]$, which equals $\sum_t\mathbb P[Q(t,S^t)]$ by the tower property. The maximum $\max_{a,j}\partial r(a,j)$ is replaced by an arbitrary upper bound $C$ of the compensations of feasible actions (infeasible actions carry reward $-\infty$ in the paper and are never taken by Online). Integrability of the regret is assumed explicitly; under the standing assumption the regret is bounded, so this is a measurability requirement.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 12, Lemma 1 (second statement)

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem

namespace BayesProphet.MultiSec

theorem compensated_coupling_expectation {S Θ A : Type*} (P : OnlineProblem S Θ A)
    (hP : P.StandingAssumption) (T : ℕ) (π : Policy S Θ A) (hπ : P.IsOnlinePolicy T π)
    (s₀ : S) {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (X : Ω → ℕ → Θ)
    (hint : MeasureTheory.Integrable (fun ω => P.regret π T s₀ (X ω)) μ)
    (C : ℝ)
    (hC : ∀ t ∈ Finset.Icc 1 T, ∀ (s : S), ∀ a ∈ P.feasible s, ∀ ω : Ω,
      P.margComp (X ω) t a s ≤ C) :
    ∫ ω, P.regret π T s₀ (X ω) ∂μ ≤
      C * ∑ t ∈ Finset.Icc 1 T,
        (μ {ω | P.Disagree (X ω) t (π t (X ω) (P.onlineState π T s₀ (X ω) t))
          (P.onlineState π T s₀ (X ω) t)}).toReal := by sorry

end BayesProphet.MultiSec
