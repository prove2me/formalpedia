-- Prove2me | Theorems.Thm_ErlangA_Staffing_lemma_2
-- name    : ErlangA.Staffing.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:45.003564+00:00
-- url     : https://prove2.me/theorems/f079e7d9-1a46-40df-8d49-e427683db22d
-- title:
--   Lemma 2 — $\sqrt N\,P_N\{Ab\}\to[\sqrt{\theta/\mu}\,h(\beta\sqrt{\mu/\theta})-\beta]\,w(-\beta,\sqrt{\mu/\theta})$
-- statement:
--   For a sequence of Erlang-A queues with $N\ge1$ agents, arrival rates $\lambda_N>0$, fixed service rate $\mu>0$ and patience rates $\theta_N>0$, let $\rho_N=\lambda_N/(N\mu)$ and assume
--   $$
--   \lim_{N\to\infty}\sqrt N(1-\rho_N)=\beta\in\mathbb R,\qquad \lim_{N\to\infty}\theta_N=\theta\in(0,\infty).
--   $$
--   Then
--   $$
--   \lim_{N\to\infty}\sqrt N\,P_N\{Ab\}=\Bigl[\sqrt{\theta/\mu}\cdot h\bigl(\beta\sqrt{\mu/\theta}\bigr)-\beta\Bigr]\cdot w\bigl(-\beta,\sqrt{\mu/\theta}\bigr),
--   $$
--   with $h$ the standard normal hazard rate and $w(x,y)=[1+h(-xy)/(y\,h(x))]^{-1}$.
--
--   So under square-root staffing the abandonment probability is of exact order $1/\sqrt N$; this is the abandonment half of the "in which case" clause of Theorem 4.
--
--   **Formalization Note** The lemma's standing hypotheses are those of Theorem 2\* (p. 223): the QED scaling and $\theta_N\to\theta$. Theorem 4 itself fixes $\theta_N\equiv\theta$; the lemma is stated in the paper's more general setting.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 226, Lemma 2

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_ErlangA_Staffing_Model
open Filter Topology DimCallCenters.Rationalized

namespace ErlangA.Staffing

/-- **Lemma 2** (p. 226). Under `√N(1 − ρ_N) → β ∈ ℝ` (`ρ_N = λ_N/(Nμ)`) and
`θ_N → θ ∈ (0, ∞)`: `√N P_N{Ab} → [√(θ/μ)·h(β√(μ/θ)) − β]·w(−β, √(μ/θ))`. -/
theorem lemma_2 (μ θ β : ℝ) (lam θN : ℕ → ℝ) (hμ : 0 < μ)
    (hlam : ∀ N : ℕ, 1 ≤ N → 0 < lam N) (hθN : ∀ N : ℕ, 1 ≤ N → 0 < θN N)
    (hθ : 0 < θ) (hθlim : Tendsto θN atTop (𝓝 θ))
    (hβ : Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / ((N : ℝ) * μ))) atTop (𝓝 β)) :
    Tendsto (fun N : ℕ => Real.sqrt N * ErlangA.Abandonment.probAbandon N (lam N) μ (θN N)) atTop
      (𝓝 ((Real.sqrt (θ / μ) * hazard (β * Real.sqrt (μ / θ)) - β) *
        w (-β) (Real.sqrt (μ / θ)))) := by sorry

end ErlangA.Staffing
