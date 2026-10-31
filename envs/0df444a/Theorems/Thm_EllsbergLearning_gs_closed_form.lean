-- Prove2me | Theorems.Thm_EllsbergLearning_gs_closed_form
-- name    : EllsbergLearning.gs_closed_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:20:50.679176+00:00
-- url     : https://prove2.me/theorems/019156f6-3341-4306-952c-d302f342e619
-- title:
--   §5.1, p.24 — the Gilboa–Schmeidler utilities in closed form
-- statement:
--   Under the standing assumptions, for every time $t$ and signal value $z$,
--   $$\min_{\mu\in\mathcal M_t}\int u(a_0,\theta)\,d\mu=(u_{00}-u_{01})(1-\overline m_t(z))+u_{01},\qquad \min_{\mu\in\mathcal M_t}\int u(a_1,\theta)\,d\mu=(u_{11}-u_{10})\underline m_t(z)+u_{10}.$$
--   The worst case for the bet $a_0$ (good under $\theta_0$) is the posterior most favourable to $\theta_1$, and vice versa; this computes the payoff $X$ of (16).
--
--   Differences from the source:
--   - encoding: posteriors $\underline m_t,\overline m_t$ by Bayesian updating (Liptser–Shiryaev, Theorem 9.1) → the closed form (12)–(13), as a function of $(t,z)$; reason: the paper's own formula; same objects
--   - generalization: times $t\ge 0$ → every real $t$ for the deterministic functions of $(t,z)$; reason: the closed forms (12)–(13) are defined for every real $t$; restricting to $t\ge0$ gives the paper's statement
-- source:
--   Epstein & Ji, Optimal Learning under Robustness and Time-Consistency, arXiv:1708.01890v2, §5.1, p.24

import Definitions.Def_EllsbergLearning_Params

open Set

namespace EllsbergLearning

/-- The Gilboa–Schmeidler utilities in closed form (Epstein & Ji, *Optimal Learning under
Robustness and Time-Consistency*, arXiv:1708.01890v2, §5.1, p.24): under the standing assumptions
of §3.1, for every time `t` and signal `z`,
`min_{µ ∈ M_t} ∫ u(a₀, θ) dµ = (u₀₀ − u₀₁)(1 − m̄_t) + u₀₁` and
`min_{µ ∈ M_t} ∫ u(a₁, θ) dµ = (u₁₁ − u₁₀)m̲_t + u₁₀`. -/
theorem gs_closed_form (p : Params) (hp : p.Valid) (t z : ℝ) :
    p.gs 0 t z = (p.u 0 0 - p.u 0 1) * (1 - p.mUp t z) + p.u 0 1 ∧
      p.gs 1 t z = (p.u 1 1 - p.u 1 0) * p.mLo t z + p.u 1 0 := by sorry

end EllsbergLearning
