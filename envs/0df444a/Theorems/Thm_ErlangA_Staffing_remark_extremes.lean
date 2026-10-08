-- Prove2me | Theorems.Thm_ErlangA_Staffing_remark_extremes
-- name    : ErlangA.Staffing.remark_extremes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:07.57046+00:00
-- url     : https://prove2.me/theorems/dfa77dda-de97-42ae-918d-238752b81e90
-- title:
--   Remark after Theorem 4 — the extremes $\beta=\mp\infty$ iff $\alpha=1,0$ iff $\Delta=\infty,0$
-- statement:
--   For a sequence of Erlang-A queues with $N\ge1$ agents, arrival rates $\lambda_N>0$, fixed service rate $\mu>0$ and constant patience rate $\theta_N\equiv\theta\in(0,\infty)$, let $\rho_N=\lambda_N/(N\mu)$. Then
--
--   1. the following are equivalent:
--   $$
--   \lim_{N\to\infty}\sqrt N(1-\rho_N)=-\infty,\qquad \lim_{N\to\infty}P_N\{W>0\}=1,\qquad \lim_{N\to\infty}\sqrt N\,P_N\{Ab\}=\infty;
--   $$
--   2. the following are equivalent:
--   $$
--   \lim_{N\to\infty}\sqrt N(1-\rho_N)=+\infty,\qquad \lim_{N\to\infty}P_N\{W>0\}=0,\qquad \lim_{N\to\infty}\sqrt N\,P_N\{Ab\}=0.
--   $$
--
--   These are the degenerate counterparts of Theorem 4: heavily overloaded systems (efficiency-driven) and lightly loaded ones (quality-driven). They are what excludes the extremes in the converse directions of Theorem 4.
--
--   **Formalization Note** The Remark's "$\beta=\pm\infty$", "$\alpha$", "$\Delta$" are read with the limits of Theorem 4: divergence of $\sqrt N(1-\rho_N)$ to $\mp\infty$ (`atBot`/`atTop`) and of $\sqrt N P_N\{Ab\}$ to $+\infty$ (`atTop`).
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 219, Remark after Theorem 4

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_ErlangA_Staffing_Model
open Filter Topology DimCallCenters.Rationalized

namespace ErlangA.Staffing

/-- **Remark after Theorem 4** (p. 219): the extremes. With `θ_N ≡ θ ∈ (0, ∞)`, `μ > 0`,
`λ_N > 0` for `N ≥ 1` and `ρ_N = λ_N/(Nμ)`:
(1) `√N(1 − ρ_N) → −∞` iff `P_N{W > 0} → 1` iff `√N P_N{Ab} → ∞`;
(2) `√N(1 − ρ_N) → +∞` iff `P_N{W > 0} → 0` iff `√N P_N{Ab} → 0`. -/
theorem remark_extremes (μ θ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (hθ : 0 < θ)
    (hlam : ∀ N : ℕ, 1 ≤ N → 0 < lam N) :
    List.TFAE
        [Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / ((N : ℝ) * μ))) atTop atBot,
         Tendsto (fun N : ℕ => probWait N (lam N) μ θ) atTop (𝓝 1),
         Tendsto (fun N : ℕ => Real.sqrt N * ErlangA.Abandonment.probAbandon N (lam N) μ θ) atTop atTop] ∧
      List.TFAE
        [Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / ((N : ℝ) * μ))) atTop atTop,
         Tendsto (fun N : ℕ => probWait N (lam N) μ θ) atTop (𝓝 0),
         Tendsto (fun N : ℕ => Real.sqrt N * ErlangA.Abandonment.probAbandon N (lam N) μ θ) atTop (𝓝 0)] := by sorry

end ErlangA.Staffing
