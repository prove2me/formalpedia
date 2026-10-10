-- Prove2me | Theorems.Thm_CoherentSDDP_Inner_qstage_convex
-- name    : CoherentSDDP.Inner.qstage_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:41.088805+00:00
-- url     : https://prove2.me/theorems/6f459e1b-d661-45cb-b984-cc50347dac8c
-- title:
--   (9), p. 11, and proof of Proposition 5, p. 16 — the stage value q_t(x_{t−1}, ω_t) of (13) is convex in x_{t−1}
-- statement:
--   In the setting of the model file, fix a stage $t$ and suppose, if $t<T$, that no bound $q^j_{t+1}$ equals $-\infty$. Then for every outcome $\omega_t$ the optimal value
--   $$
--   q_t(x_{t-1},\omega_t)=\min\Big\{c_t^\top x_t+\hat{\mathcal Q}_{t+1}(x_t):\ A_tx_t=b_t(\omega_t)-E_tx_{t-1},\ x_t\ge0\Big\}
--   $$
--   of the policy's stage problem (13) is a convex function of the state $x_{t-1}$, as an extended-real function (convex epigraph; the value $+\infty$ marks an infeasible stage problem).
--
--   The paper uses this convexity twice: to derive (9), $q_t(x_{t-1},\omega_t)\le\sum_j\lambda^jq_t(x^j_{t-1},\omega_t)$ when $x_{t-1}=\sum_j\lambda^jx^j_{t-1}$, and in the base case of the proof of Proposition 5.
--
--   **Formalization Note** The statement covers the stages $t\ge T$, where $\hat{\mathcal Q}_{t+1}\equiv0$ and no hypothesis on the bounds is needed. The hypothesis $q^j_{t+1}\neq-\infty$ (for $t<T$) reflects that the bounds are upper bounds on costs; it follows from the upper-bound hypothesis of the goal theorem.
-- source:
--   Philpott, de Matos & Finardi, On Solving Multistage Stochastic Programs with Coherent Risk Measures, authors' manuscript of 13 August 2012 (Operations Research, 2013), p. 11, (9) 'by convexity of q_t(x_{t−1}, ω_t)'; p. 16, proof of Proposition 5, 'the convexity of q_T(x_{T−1}, ω_T)'; p. 17, (13)

import Mathlib
import Definitions.Def_CoherentSDDP_Inner_Basic
import Definitions.Def_CoherentSDDP_Inner_Model

namespace CoherentSDDP.Inner

theorem qstage_convex {n m : ℕ} {Ω : ℕ → Type} (M : Model n m Ω) (D : InnerData n) (t : ℕ)
    (hqv : t < M.T → ∀ j, D.qv (t + 1) j ≠ ⊥) :
    ∀ ω : Ω t, EConvex (fun xprev => qstage M D t xprev ω) := by sorry

end CoherentSDDP.Inner
