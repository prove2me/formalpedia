-- Prove2me | Theorems.Thm_DualMoments_RiskPremium_rdu_risk_premium_approx
-- name    : DualMoments.RiskPremium.rdu_risk_premium_approx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:43.13097+00:00
-- url     : https://prove2.me/theorems/2826fb12-6a24-4c58-9499-a10212d0f7db
-- title:
--   (4.3), §4, p. 8 — the RDU risk premium is m2/(2Pr)·(−U″/U′) + m̄2/(2Pr)·(−h″/h′) + o(ε2² + ε1ε2) as (ε1, ε2) → (0⁺, 0⁺)
-- statement:
--   Let $U$ be twice continuously differentiable with $U' > 0$ (the utility), let $h$ be a probability weighting function, twice continuously differentiable on $[0,1]$ with $h(0) = 0$, $h(1) = 1$ and $h' > 0$, let $0 < p_0 < 1$ and let $w_0 \in \mathbb R$ be the initial wealth. For every $\varepsilon_1 \in (0, \min\{p_0, 1 - p_0\})$ and $\varepsilon_2 > 0$ let $\lambda(\varepsilon_1, \varepsilon_2)$ be an RDU risk premium for the change from lottery $C$ ($w_0 \mp \varepsilon_2$ with probabilities $p_0$, $1 - p_0$) to lottery $D$ (which moves mass $\varepsilon_1$ from each branch of $C$ to a middle outcome $w_0 - \lambda$), that is, a solution of (4.2) with $-\varepsilon_2 < -\lambda < \varepsilon_2$.
--
--   Let $m_2$, $\bar m_2$ and $\Pr$ be the unconditional variance, maxiance and total mass of the risk $\tilde\varepsilon_{12}$ ($\pm\varepsilon_2$, each with probability $\varepsilon_1$). Then, as $(\varepsilon_1, \varepsilon_2) \to (0^+, 0^+)$ jointly,
--   $$\lambda = \frac{m_2}{2\Pr}\left(-\frac{U''(w_0)}{U'(w_0)}\right) + \frac{\bar m_2}{2\Pr}\left(-\frac{h''(p_0)}{h'(p_0)}\right) + o\!\left(\frac{m_2}{\Pr} + \frac{\bar m_2}{\Pr}\right).$$
--
--   This is the paper's local index of risk aversion under rank-dependent utility: the premium of a small risk aggregates the Pratt–Arrow term (variance times utility risk aversion) and the dual-theory term (maxiance times probability-weighting risk aversion), with variance and maxiance on an equal footing.
--
--   **Formalization Note** The paper's "$\lambda \simeq$", obtained by Taylor expansions to first order in $\lambda$ and second order in $\varepsilon_1, \varepsilon_2$, is read as a little-o statement in the joint one-sided limit $(\varepsilon_1, \varepsilon_2) \to (0^+, 0^+)$ (the filter $\mathcal N_{(0,0)}$ restricted to $(0,\infty)^2$), with remainder small relative to $m_2/\Pr + \bar m_2/\Pr = \varepsilon_2^2 + \varepsilon_1\varepsilon_2$, the size of the two leading terms. A limit in $\varepsilon_2$ alone at fixed $\varepsilon_1$ would be false: the dual term then carries a relative error of order $\varepsilon_1$. The premium is any function $\lambda(\varepsilon_1, \varepsilon_2)$ satisfying the indifference on the feasible region; the milestone for (4.2) shows it exists and is unique. The moments are computed from $\tilde\varepsilon_{12}$, not hard-coded; $\Pr = 2\varepsilon_1 > 0$ on the filter. $U''(w_0)$ and $h''(p_0)$ are iterated ordinary derivatives (`deriv (deriv ·)`), which are the true second derivatives here since $p_0$ is interior.
-- source:
--   Eeckhoudt & Laeven, Dual Moments and Risk Attitudes, arXiv:1612.03347v2, (4.3), §4, p. 8, with footnote 21

import Mathlib
import Definitions.Def_DualMoments_RiskPremium_Model

namespace DualMoments.RiskPremium

open Filter Asymptotics Topology in
theorem rdu_risk_premium_approx (U h : ℝ → ℝ) (hU : UtilityStanding U)
    (hh : WeightingStanding h) (p0 w0 : ℝ) (hp0 : 0 < p0 ∧ p0 < 1) (lam : ℝ → ℝ → ℝ)
    (hlam : ∀ ε₁ ε₂, Feasible p0 ε₁ → 0 < ε₂ → IsRDUPremium U h p0 w0 ε₁ ε₂ (lam ε₁ ε₂)) :
    (fun e : ℝ × ℝ => lam e.1 e.2 -
        ((risk12 e.1 e.2).variance / (2 * (risk12 e.1 e.2).mass) *
            (-(deriv (deriv U) w0) / deriv U w0) +
          (risk12 e.1 e.2).maxiance / (2 * (risk12 e.1 e.2).mass) *
            (-(deriv (deriv h) p0) / deriv h p0)))
      =o[𝓝[Set.Ioi 0 ×ˢ Set.Ioi 0] ((0 : ℝ), (0 : ℝ))]
    (fun e : ℝ × ℝ => (risk12 e.1 e.2).variance / (risk12 e.1 e.2).mass +
        (risk12 e.1 e.2).maxiance / (risk12 e.1 e.2).mass) := by sorry

end DualMoments.RiskPremium
