-- Prove2me | Theorems.Thm_ErlangA_Staffing_theorem_4
-- name    : ErlangA.Staffing.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:38.528696+00:00
-- url     : https://prove2.me/theorems/8403c755-9798-45f8-afd1-826c388c63e4
-- title:
--   Theorem 4 — square-root staffing $\iff$ $P_N\{W>0\}\to\alpha\in(0,1)$ $\iff$ $\sqrt N P_N\{Ab\}\to\Delta\in(0,\infty)$
-- statement:
--   Consider a sequence of Erlang-A ($M/M/N+M$) call centers indexed by the number of agents $N\ge1$: the $N$-th has Poisson arrivals at rate $\lambda_N>0$, exponential service at a fixed rate $\mu>0$, and exponential patience at a fixed rate $\theta_N\equiv\theta$ with $0<\theta<\infty$. Let $\rho_N=\lambda_N/(N\mu)$ be the offered load per agent, $P_N\{W>0\}$ the steady-state probability that an arriving customer waits, and $P_N\{Ab\}$ the steady-state probability that an arriving customer abandons. Then the following three conditions are equivalent:
--
--   1. $\displaystyle\lim_{N\to\infty}\sqrt N(1-\rho_N)=\beta$ for some $-\infty<\beta<\infty$;
--   2. $\displaystyle\lim_{N\to\infty}P_N\{W>0\}=\alpha$ for some $0<\alpha<1$;
--   3. $\displaystyle\lim_{N\to\infty}\sqrt N\,P_N\{Ab\}=\Delta$ for some $0<\Delta<\infty$;
--
--   in which case
--   $$
--   \alpha=w\bigl(-\beta,\sqrt{\mu/\theta}\bigr),\qquad \Delta=\Bigl[\sqrt{\theta/\mu}\cdot h\bigl(\beta\sqrt{\mu/\theta}\bigr)-\beta\Bigr]\cdot\alpha,
--   $$
--   where $h(x)=\varphi(x)/[1-\Phi(x)]$ is the standard normal hazard rate and $w(x,y)=[1+h(-xy)/(y\,h(x))]^{-1}$.
--
--   The theorem characterizes the quality-and-efficiency-driven (QED) regime for call centers with impatient customers: square-root safety staffing $N\approx R+\beta\sqrt R$, $R=\lambda/\mu$, is exactly the regime in which the delay probability is nondegenerate and the abandonment probability is of order $1/\sqrt N$. Unlike the Halfin–Whitt theorem for $M/M/N$ queues, $\beta$ may be negative.
--
--   **Formalization Note** The conclusion is a conjunction: (a) the three existential conditions are pairwise equivalent (`List.TFAE`), and (b) for every real $\beta$, convergence $\sqrt N(1-\rho_N)\to\beta$ implies convergence of $P_N\{W>0\}$ and $\sqrt N P_N\{Ab\}$ to the displayed values, which is the "in which case" clause. $P_N\{W>0\}$ is $\sum_{k\ge N}\pi^{(N)}_k$ and $P_N\{Ab\}$ is defined in `ErlangA.Staffing.Model`. Hypotheses on the $N$-th system are imposed for $N\ge1$; the value at $N=0$ is irrelevant to the limits.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 219, Theorem 4

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_ErlangA_Staffing_Model
open Filter Topology DimCallCenters.Rationalized

namespace ErlangA.Staffing

/-- **Theorem 4** (p. 219). Assume `θ_N ≡ θ`, `0 < θ < ∞`, with `μ > 0`, `λ_N > 0` for `N ≥ 1`
and `ρ_N = λ_N/(Nμ)`. Then the following are equivalent:
`lim √N(1 − ρ_N) = β` for some finite `β`; `lim P_N{W > 0} = α` for some `0 < α < 1`;
`lim √N P_N{Ab} = Δ` for some `0 < Δ < ∞`. In which case `α = w(−β, √(μ/θ))` and
`Δ = [√(θ/μ)·h(β√(μ/θ)) − β]·α`. -/
theorem theorem_4 (μ θ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (hθ : 0 < θ)
    (hlam : ∀ N : ℕ, 1 ≤ N → 0 < lam N) :
    List.TFAE
        [∃ β : ℝ,
            Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / ((N : ℝ) * μ))) atTop (𝓝 β),
         ∃ α ∈ Set.Ioo (0 : ℝ) 1,
            Tendsto (fun N : ℕ => probWait N (lam N) μ θ) atTop (𝓝 α),
         ∃ Δ ∈ Set.Ioi (0 : ℝ),
            Tendsto (fun N : ℕ => Real.sqrt N * ErlangA.Abandonment.probAbandon N (lam N) μ θ) atTop (𝓝 Δ)] ∧
      ∀ β : ℝ,
        Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / ((N : ℝ) * μ))) atTop (𝓝 β) →
          Tendsto (fun N : ℕ => probWait N (lam N) μ θ) atTop
              (𝓝 (w (-β) (Real.sqrt (μ / θ)))) ∧
            Tendsto (fun N : ℕ => Real.sqrt N * ErlangA.Abandonment.probAbandon N (lam N) μ θ) atTop
              (𝓝 ((Real.sqrt (θ / μ) * hazard (β * Real.sqrt (μ / θ)) - β) *
                w (-β) (Real.sqrt (μ / θ)))) := by sorry

end ErlangA.Staffing
