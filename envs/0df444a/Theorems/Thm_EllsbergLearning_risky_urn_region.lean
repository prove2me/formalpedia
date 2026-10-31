-- Prove2me | Theorems.Thm_EllsbergLearning_risky_urn_region
-- name    : EllsbergLearning.risky_urn_region
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:02.520629+00:00
-- url     : https://prove2.me/theorems/656bc614-3205-4da5-8a0d-5c5a53dd343a
-- title:
--   §5.3, p.32 — the risky urn loses iff $|Z_t|\ge\bar{\bar z}$, and $\bar{\bar z}<\overline z$ (corrected: (19))
-- statement:
--   In the Ellsberg model with $0<\alpha<\tfrac12$, $0<\epsilon<1$, $\sigma>0$, let $\bar{\bar z}=\frac{\sigma^2}{2\alpha}\log\frac{1+\epsilon}{1-\epsilon}$.
--
--   1. At every time $t$ and signal $z$ (not necessarily a stopping time), betting on the ambiguous urn (on red or on blue, whichever is better) is weakly preferred to betting on the risky urn iff $|z|\ge\bar{\bar z}$, and strictly preferred iff $|z|>\bar{\bar z}$.
--   2. If moreover $c>0$, $\hat r\in(0,1)$ solves (22), $\frac{1+\epsilon}{2}<\hat r$, and $\bar r\in(0,1)$ solves (24), then $\bar{\bar z}<\overline z$, with $\overline z$ of (23).
--
--   Hence at the optimal stopping time of Theorem 3.1(ii), where $|Z_{\tau^*}|=\overline z>\bar{\bar z}$, the risky urn is never chosen.
--
--   Differences from the source:
--   - correction: (19): $u(a_0,\alpha)=u(a_1,-\alpha)=\alpha-\tfrac12$ → $u(a_0,\alpha)=u(a_1,-\alpha)=\tfrac12-\alpha$; reason: the printed value is negative for every $0<\alpha<1/2$, against the nonnegativity of payoffs assumed on p.11; the paper's (20) (p.13), $u_2=\tfrac12(u_{00}+u_{10})$ (p.19) and $u_{11}-u_{10}=2\alpha$ used in the proof (p.31) all require $\tfrac12-\alpha$ (prizes 1 and 0)
--   - encoding: posteriors $\underline m_t,\overline m_t$ by Bayesian updating (Liptser–Shiryaev, Theorem 9.1) → the closed form (12)–(13), as a function of $(t,z)$; reason: the paper's own formula; same objects
--   - generalization: times $t\ge 0$ → every real $t$ for the deterministic functions of $(t,z)$; reason: the closed forms (12)–(13) are defined for every real $t$; restricting to $t\ge0$ gives the paper's statement
--   - reading: "betting on the ambiguous urn is preferred to betting on the risky urn iff $|Z_t|\ge\bar{\bar z}$" → weak preference ($\ge$) iff $|z|\ge\bar{\bar z}$, and strict preference iff $|z|>\bar{\bar z}$; reason: "preferred" with the non-strict $\ge$ of the page is weak preference; the strict version is added
-- source:
--   Epstein & Ji, Optimal Learning under Robustness and Time-Consistency, arXiv:1708.01890v2, §5.3, p.32

import Definitions.Def_EllsbergLearning_CriticalValues
import Definitions.Def_EllsbergLearning_Ellsberg

open Set

namespace EllsbergLearning

/-- The risky urn loses exactly when `|Z_t| ≥ z̿` (Epstein & Ji, arXiv:1708.01890v2, §5.3, p.32).
In the Ellsberg model with `0 < α < 1/2`, `0 < ϵ < 1`, `σ > 0`, and
`z̿ = σ²/(2α) log((1 + ϵ)/(1 − ϵ))`:

1. at every time `t` and signal `z`, betting on the ambiguous urn (on red or on blue) is weakly
   preferred to betting on the risky urn iff `|z| ≥ z̿`, and strictly preferred iff `|z| > z̿`
   (the better of the two Gilboa–Schmeidler utilities compared with `u₂ = 1/2`);
2. if moreover `c > 0`, `r̂ ∈ (0, 1)` solves (22), `(1 + ϵ)/2 < r̂`, and `r̄ ∈ (0, 1)` solves (24),
   then `z̿ < z̄`, with `z̄` of (23). -/
theorem risky_urn_region (α ϵ σ c : ℝ) (hα : 0 < α) (hα' : α < 1 / 2) (hϵ : 0 < ϵ)
    (hϵ' : ϵ < 1) (hσ : 0 < σ) :
    let p := ellsberg α ϵ σ c
    (∀ t z : ℝ,
      (p.u₂ ≤ max (p.gs 0 t z) (p.gs 1 t z) ↔ zbarbar α ϵ σ ≤ |z|) ∧
      (p.u₂ < max (p.gs 0 t z) (p.gs 1 t z) ↔ zbarbar α ϵ σ < |z|)) ∧
    (0 < c → ∀ rhat : ℝ, rhat ∈ Ioo (0 : ℝ) 1 → ell rhat = 2 * α ^ 3 / (c * σ ^ 2) →
      (1 + ϵ) / 2 < rhat → ∀ rbar : ℝ, rbar ∈ Ioo (0 : ℝ) 1 →
      ell rbar + ell ((1 + ϵ) / 2) = 4 * α ^ 3 / (c * σ ^ 2) →
      zbarbar α ϵ σ < zbar α ϵ σ rbar) := by sorry

end EllsbergLearning
