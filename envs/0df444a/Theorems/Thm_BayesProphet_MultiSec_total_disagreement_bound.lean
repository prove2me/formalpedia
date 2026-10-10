-- Prove2me | Theorems.Thm_BayesProphet_MultiSec_total_disagreement_bound
-- name    : BayesProphet.MultiSec.total_disagreement_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:39.157901+00:00
-- url     : https://prove2.me/theorems/22758e0e-f390-443c-ab01-857549e3972f
-- title:
--   App. B.3 — total compensation $\sum_{t\le T}q(t,B^t)\le\sum_{j>1}2/p_j$
-- statement:
--   Under the hypotheses of the multi-secretary analysis ($p_j>0$, $\sum_jp_j=1$, $r_1\ge\dots\ge r_n\ge0$), for every horizon $T$ and every sequence of budgets $(B^t)_{t\in[T]}$,
--   $$\sum_{t\le T}q(t,B^t)\ \le\ \sum_{j>1}p_j\sum_{t\le T}e^{-p_j^2t/2}\ \le\ \sum_{j>1}p_j\,\frac{2}{p_j^2},$$
--   where $q(t,b)=\sum_jp_j\,q_j(t,b)$ is the probability that Offline is not satisfied with the Fluid Bayes Selector's action at time-to-go $t$ with budget $b$, and the sums over $t$ run over $t=1,\dots,T$.
--
--   This bounds the expected number of disagreements of the policy by a constant independent of $T$ and of the budgets.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 37, Appendix B.3, display before 'Using compensated coupling (Lemma 1)'

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem
import Definitions.Def_BayesProphet_MultiSec_MultiSecretary

namespace BayesProphet.MultiSec

theorem total_disagreement_bound {n : ℕ} [NeZero n] (p r : Fin n → ℝ) (hp : ∀ j, 0 < p j)
    (hsum : ∑ j, p j = 1) (hr : Antitone r) (hr₀ : ∀ j, 0 ≤ r j)
    (T : ℕ) (bud : ℕ → ℕ) :
    ∑ t ∈ Finset.Icc 1 T, disagreeProb p r t (bud t) ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin n),
          p j * ∑ t ∈ Finset.Icc 1 T, Real.exp (-(p j ^ 2 * t / 2)) ∧
    ∑ j ∈ Finset.univ.erase (0 : Fin n),
          p j * ∑ t ∈ Finset.Icc 1 T, Real.exp (-(p j ^ 2 * t / 2)) ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin n), p j * (2 / p j ^ 2) := by sorry

end BayesProphet.MultiSec
