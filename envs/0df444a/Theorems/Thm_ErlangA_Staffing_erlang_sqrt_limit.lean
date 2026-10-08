-- Prove2me | Theorems.Thm_ErlangA_Staffing_erlang_sqrt_limit
-- name    : ErlangA.Staffing.erlang_sqrt_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:42.242583+00:00
-- url     : https://prove2.me/theorems/6d444008-ed2a-4b20-b976-a6e0d8fc5941
-- title:
--   Proof of Theorem 4 — Erlang-B in the square-root regime: $\sqrt N\,P_N\{Bl\}\to h(-\beta)$
-- statement:
--   Let $\mu>0$, let $\lambda_N>0$ for $N\ge1$, and let $P_N\{Bl\}=E(\lambda_N/\mu,N)$ be Erlang's loss formula for $N$ servers and offered load $\lambda_N/\mu$. If
--   $$
--   \lim_{N\to\infty}\sqrt N\Bigl(1-\frac{\lambda_N}{N\mu}\Bigr)=\beta\in\mathbb R,
--   $$
--   then
--   $$
--   \lim_{N\to\infty}\sqrt N\,P_N\{Bl\}=h(-\beta)=\frac{\varphi(\beta)}{\Phi(\beta)},
--   $$
--   where $\varphi$, $\Phi$ are the standard normal density and distribution function and $h$ is the standard normal hazard rate.
--
--   This is the classical square-root asymptotic of the Erlang-B formula (Jagerman 1974), the input to Lemma 2 and to the bound $\Delta\le\lim_{\beta\to\infty}h(-\beta)=0$ in the proof of Theorem 4.
--
--   **Formalization Note** The paper displays it as the inner limit of $\lim_{\beta\to\infty}\lim_{N\to\infty}\sqrt N P_N\{Bl\}=\lim_{\beta\to\infty}h(-\beta)$; the milestone is that inner limit, for every real $\beta$.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 226, Appendix C, proof of Theorem 4, β → ∞ display (inner limit)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_ErlangA_Staffing_Model
open Filter Topology DimCallCenters.Rationalized

namespace ErlangA.Staffing

/-- **Erlang-B in the square-root regime** (proof of Theorem 4, p. 226, the inner limit
`lim_{N→∞} √N P_N{Bl} = h(−β)`). If `μ > 0`, `λ_N > 0` for `N ≥ 1` and
`√N(1 − λ_N/(Nμ)) → β ∈ ℝ`, then `√N · P_N{Bl} → h(−β) = φ(β)/Φ(β)`. -/
theorem erlang_sqrt_limit (μ β : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ)
    (hlam : ∀ N : ℕ, 1 ≤ N → 0 < lam N)
    (hβ : Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / ((N : ℝ) * μ))) atTop (𝓝 β)) :
    Tendsto (fun N : ℕ => Real.sqrt N * probBlock N (lam N) μ) atTop (𝓝 (hazard (-β))) := by sorry

end ErlangA.Staffing
