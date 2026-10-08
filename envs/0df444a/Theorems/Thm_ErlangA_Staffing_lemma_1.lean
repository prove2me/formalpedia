-- Prove2me | Theorems.Thm_ErlangA_Staffing_lemma_1
-- name    : ErlangA.Staffing.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:36.575298+00:00
-- url     : https://prove2.me/theorems/fbac6c76-145e-4f3c-b8f6-0bcfad373c4f
-- title:
--   Lemma 1 ($0<\theta<\infty$) — $P_N\{W>0\}\to w(-\beta,\sqrt{\mu/\theta})$
-- statement:
--   For a sequence of Erlang-A queues with $N\ge1$ agents, arrival rates $\lambda_N>0$, fixed service rate $\mu>0$ and patience rates $\theta_N>0$, let $\rho_N=\lambda_N/(N\mu)$ and assume
--   $$
--   \lim_{N\to\infty}\sqrt N(1-\rho_N)=\beta\in\mathbb R,\qquad \lim_{N\to\infty}\theta_N=\theta\in(0,\infty).
--   $$
--   Then the steady-state probability that an arriving customer has to wait converges:
--   $$
--   \lim_{N\to\infty}P_N\{W>0\}=w\bigl(-\beta,\sqrt{\mu/\theta}\bigr),
--   $$
--   where $w(x,y)=[1+h(-xy)/(y\,h(x))]^{-1}$ and $h$ is the standard normal hazard rate.
--
--   This is the delay-probability half of the "in which case" clause of Theorem 4; it holds for $\beta$ of either sign.
--
--   **Formalization Note** Only the case $0<\theta<\infty$ of the paper's three-case Lemma 1 is stated. $P_N\{W>0\}$ is $\sum_{k\ge N}\pi^{(N)}_k$; the proof on p. 226 writes $P\{Q_N(\infty)>N\}$, which differs by $\pi^{(N)}_N\to0$, so the limits coincide.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 226, Lemma 1 (case 0 < θ < ∞)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_ErlangA_Staffing_Model
open Filter Topology DimCallCenters.Rationalized

namespace ErlangA.Staffing

/-- **Lemma 1**, case `0 < θ < ∞` (p. 226). Under `√N(1 − ρ_N) → β ∈ ℝ`
(`ρ_N = λ_N/(Nμ)`) and `θ_N → θ ∈ (0, ∞)`, the steady-state delay probability converges:
`P_N{W > 0} → w(−β, √(μ/θ))`. -/
theorem lemma_1 (μ θ β : ℝ) (lam θN : ℕ → ℝ) (hμ : 0 < μ)
    (hlam : ∀ N : ℕ, 1 ≤ N → 0 < lam N) (hθN : ∀ N : ℕ, 1 ≤ N → 0 < θN N)
    (hθ : 0 < θ) (hθlim : Tendsto θN atTop (𝓝 θ))
    (hβ : Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / ((N : ℝ) * μ))) atTop (𝓝 β)) :
    Tendsto (fun N : ℕ => probWait N (lam N) μ (θN N)) atTop
      (𝓝 (w (-β) (Real.sqrt (μ / θ)))) := by sorry

end ErlangA.Staffing
