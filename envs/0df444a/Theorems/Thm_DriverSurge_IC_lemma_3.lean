-- Prove2me | Theorems.Thm_DriverSurge_IC_lemma_3
-- name    : DriverSurge.IC.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:05.142981+00:00
-- url     : https://prove2.me/theorems/9c7b797b-1168-44a8-9d88-db1c0da3255d
-- title:
--   Lemma 3, p. 12 — the long-run fraction of time open in state i or on a trip started in i is µ_i(σ) = T_iQ_j/(T_jQ_i + T_iQ_j)
-- statement:
--   In the stochastic dynamic model with any initial world state, let a driver follow a policy $\sigma=\{\sigma_1,\sigma_2\}$ with $\tau$ $F_i$-integrable on $\sigma_i$ ($i=1,2$). Then, for each state $i$, the fraction of $[0,t]$ the driver spends either open while the world is in state $i$, or on a trip started in state $i$, converges almost surely as $t\to\infty$ to
--   $$\mu_i(\sigma)=\frac{\lambda_iF_i(\sigma_i)T_i(\sigma_i)\,Q_j(\sigma_j)}{\lambda_jF_j(\sigma_j)T_j(\sigma_j)\,Q_i(\sigma_i)+\lambda_iF_i(\sigma_i)T_i(\sigma_i)\,Q_j(\sigma_j)},\qquad Q_i(\sigma_i)=\lambda_{i\to j}+\lambda_i\int_{\sigma_i}q_{i\to j}(\tau)\,dF_i(\tau),$$
--   with $T_i(\sigma_i)$ as in Lemma 1 and $j\ne i$.
--
--   Together with Lemma 1 this expresses the driver's earnings rate in closed form, as an average of the per-state rates weighted by these occupation fractions.
--
--   **Formalization Note** Lean state `0` is the paper's non-surge state 1 and Lean state `1` the surge state 2; `other i` is the state $j\ne i$. $\lambda_iF_i(\sigma_i)T_i(\sigma_i)$ is the normalized $T_i=1+\lambda_i\int_{\sigma_i}\tau\,dF_i$, which is defined also when $F_i(\sigma_i)=0$.
--
--   Differences from the source:
--   - reading: "the fraction of time a driver … spends" → the almost-sure limit of occupation$(t)/t$ as $t\to\infty$; reason: the meaning used in the proof of Lemma 1 (p. 49)
--   - encoding: $T_i(\sigma_i)$ with $\int_{\sigma_i}\tau\,dF_i$ implicitly finite → $\tau$ assumed $F_i$-integrable on $\sigma_i$; reason: $T_i$ is undefined otherwise; only undefined cases are excluded
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, p. 12, Lemma 3

import Mathlib
import Definitions.Def_DriverSurge_IC_Process

namespace DriverSurge.IC

open MeasureTheory Filter Topology

/-- Lemma 3 (p. 12). For every policy `σ` with trip lengths integrable on `σ_1` and `σ_2`, the fraction
of `[0, t]` the driver spends open in state `i` or on a trip started in state `i` converges almost
surely to `µ_i(σ) = T_iQ_j/(T_jQ_i + T_iQ_j)`, for every initial world state. -/
theorem lemma_3 (P : Primitives) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (i₀ : Fin 2)
    (X : Ω → Path) (hX : IsDriverModel P μ i₀ X) (σ : Fin 2 → Set ℝ) (hσ : IsPolicy σ)
    (hτ : ∀ i, IntegrableOn (fun τ : ℝ => τ) (σ i) (P.F i)) (i : Fin 2) :
    ∀ᵐ ω ∂μ, Tendsto (fun t : ℝ => occupation i₀ (X ω) σ i t / t) atTop (𝓝 (mu P σ i)) := by sorry

end DriverSurge.IC
