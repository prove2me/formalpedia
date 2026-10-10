-- Prove2me | Theorems.Thm_BayesProphet_MultiSec_compensated_coupling_identity
-- name    : BayesProphet.MultiSec.compensated_coupling_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:45:45.368762+00:00
-- url     : https://prove2.me/theorems/d1d82014-7f0f-4e12-b2fb-a90e9f0ad290
-- title:
--   Lemma 1 (Compensated Coupling) — pathwise regret identity
-- statement:
--   Let an online decision problem satisfy the standing assumption, let $T\in\mathbb N$, and let $\pi^{\mathrm{on}}$ be an online policy for horizon $T$ started in state $S^T=s_0$, with state process $S^t$. Then on every sample path
--   $$\mathrm{Reg}=\sum_{t\in[T]}\partial R\big(t,\pi^{\mathrm{on}}(t,S^t,\theta^t),S^t\big)\cdot\mathbf 1_{Q(t,S^t)},$$
--   where $Q(t,S^t)=Q(t,\pi^{\mathrm{on}}(t,S^t,\theta^t),S^t)$ is the event that Offline is not satisfied with Online's action.
--
--   The identity expresses the regret of any online policy as the total compensation paid to Offline for following Online; it is the basis of every regret bound in the paper.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 12, Lemma 1 (first display)

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem

namespace BayesProphet.MultiSec

theorem compensated_coupling_identity {S Θ A : Type*} (P : OnlineProblem S Θ A)
    (hP : P.StandingAssumption) (T : ℕ) (π : Policy S Θ A) (hπ : P.IsOnlinePolicy T π)
    (s₀ : S) (θ : ℕ → Θ) :
    P.regret π T s₀ θ =
      ∑ t ∈ Finset.Icc 1 T,
        P.margComp θ t (π t θ (P.onlineState π T s₀ θ t)) (P.onlineState π T s₀ θ t) *
          P.disagreeInd θ t (π t θ (P.onlineState π T s₀ θ t)) (P.onlineState π T s₀ θ t) := by sorry

end BayesProphet.MultiSec
