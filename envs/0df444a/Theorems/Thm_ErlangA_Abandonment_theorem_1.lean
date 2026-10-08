-- Prove2me | Theorems.Thm_ErlangA_Abandonment_theorem_1
-- name    : ErlangA.Abandonment.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:42.556247+00:00
-- url     : https://prove2.me/theorems/d49c0df4-522a-479e-84f6-74f03e57703e
-- title:
--   Theorem 1 — the fraction of abandoning customers tends to $\max(0,1-1/\rho_\infty)$
-- statement:
--   Consider a sequence of Erlang-A queues indexed by the number of agents $N\ge1$: the $N$-th system has arrival rate $\lambda_N>0$, service rate $\mu>0$ (the same for all $N$) and patience rate $\theta_N>0$, and its traffic intensity is
--   $$
--   \rho_N=\frac{\lambda_N}{N\mu}.
--   $$
--   Assume, as in §4 of the paper, that $\lambda_N\to\infty$ and $\theta_N\to\theta$ with $0<\theta<\infty$. Let $P_N\{Ab\}$ be the probability that a customer arriving to the $N$-th system in steady state abandons. If $\rho_N\to\rho_\infty$ for some $0\le\rho_\infty\le\infty$, then
--   $$
--   \lim_{N\to\infty}P_N\{Ab\}=\begin{cases}0, & 0\le\rho_\infty\le1,\\[1mm] 1-\dfrac1{\rho_\infty}, & \rho_\infty>1,\end{cases}
--   $$
--   with $1-1/\infty=1$.
--
--   Thus, to leading order, the fraction of abandoning callers does not depend on the patience distribution's rate: a critically loaded center ($\rho_\infty=1$) already has vanishing abandonment, while an overloaded one sheds exactly the excess load.
--
--   **Formalization Note** The limit $\rho_\infty\in[0,\infty]$ is an extended nonnegative real, and $\rho_N\to\rho_\infty$ is convergence of $\rho_N$ in $[0,\infty]$; for $\rho_\infty=\infty$ it means $\rho_N\to\infty$. The value $1-1/\rho_\infty$ is computed in $[0,\infty]$ and converted to a real number, which gives $1$ at $\rho_\infty=\infty$. The hypotheses $\lambda_N\to\infty$ and $\theta_N\to\theta\in(0,\infty)$ are the standing assumptions of §4 and are kept as the paper states them; positivity of $\lambda_N$, $\theta_N$ is imposed for $N\ge1$.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 215, Theorem 1 (with the standing assumptions of §4, p. 215)

import Mathlib
import Definitions.Def_ErlangA_Abandonment_Model
open Filter Topology

namespace ErlangA.Abandonment

/-- **Theorem 1**, p. 215. Standing assumptions of §4 (p. 215): `μ_N ≡ μ > 0`, `λ_N > 0` with
`λ_N → ∞`, `θ_N > 0` with `θ_N → θ ∈ (0, ∞)`. If `ρ_N = λ_N/(Nμ) → ρ_∞ ∈ [0, ∞]` (convergence
in `ℝ≥0∞`), then `P_N{Ab} → 0` when `ρ_∞ ≤ 1` and `P_N{Ab} → 1 − 1/ρ_∞` when `ρ_∞ > 1`
(with `1 − 1/∞ = 1`). -/
theorem theorem_1 (μ θ : ℝ) (lam θN : ℕ → ℝ) (hμ : 0 < μ)
    (hlam : ∀ N : ℕ, 1 ≤ N → 0 < lam N) (hlam_infty : Tendsto lam atTop atTop)
    (hθN : ∀ N : ℕ, 1 ≤ N → 0 < θN N) (hθ : 0 < θ) (hθlim : Tendsto θN atTop (𝓝 θ))
    (ρinf : ENNReal)
    (hρ : Tendsto (fun N : ℕ => ENNReal.ofReal (lam N / ((N : ℝ) * μ))) atTop (𝓝 ρinf)) :
    Tendsto (fun N : ℕ => probAbandon N (lam N) μ (θN N)) atTop
      (𝓝 (if ρinf ≤ 1 then 0 else (1 - ρinf⁻¹).toReal)) := by sorry

end ErlangA.Abandonment
