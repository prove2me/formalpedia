-- Prove2me | Theorems.Thm_BayesProphet_MultiSec_cond_disagreement_bound
-- name    : BayesProphet.MultiSec.cond_disagreement_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:50.327836+00:00
-- url     : https://prove2.me/theorems/99459126-9c91-48dd-b330-538a63ab6362
-- title:
--   App. B.3 — conditional disagreement bound $q_j(t,b)\le e^{-p_j^2t/2}$
-- statement:
--   Consider the multi-secretary problem with multinomial arrivals, $p_j>0$, $\sum_jp_j=1$, rewards sorted $r_1\ge\dots\ge r_n\ge0$, and the Fluid Bayes Selector. For every time-to-go $t\ge1$ and every budget $b\in\mathbb N$:
--
--   1. for the best type, $q_1(t,b)=0$;
--   2. for every type $j>1$,
--   $$q_j(t,b)\le e^{-p_j^2t/2}.$$
--
--   Here $q_j(t,b)$ is the probability, conditioned on $\theta^t=j$, that Offline is not satisfied with the policy's action at time-to-go $t$ with budget $b$. The bound is uniform in the budget, which is what makes the regret independent of $T$ and $B$.
--
--   **Formalization Note** The paper states the bound for the budget $B^t$ reached by the policy; since $B^t$ depends only on $\theta^T,\dots,\theta^{t+1}$, which are independent of $\theta^t,\dots,\theta^1$, the statement for every fixed $b$ is the same claim. Lean index `0` is type $1$.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 37, Appendix B.3, the two displays bounding q_j(t,B^t)

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem
import Definitions.Def_BayesProphet_MultiSec_MultiSecretary

namespace BayesProphet.MultiSec

theorem cond_disagreement_bound {n : ℕ} [NeZero n] (p r : Fin n → ℝ) (hp : ∀ j, 0 < p j)
    (hsum : ∑ j, p j = 1) (hr : Antitone r) (hr₀ : ∀ j, 0 ≤ r j)
    (j : Fin n) (t b : ℕ) (ht : 1 ≤ t) :
    ((j : ℕ) = 0 → condDisagreeProb p r j t b = 0) ∧
    ((j : ℕ) ≠ 0 → condDisagreeProb p r j t b ≤ Real.exp (-(p j ^ 2 * t / 2))) := by sorry

end BayesProphet.MultiSec
