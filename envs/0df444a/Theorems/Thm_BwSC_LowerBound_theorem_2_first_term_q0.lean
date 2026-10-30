-- Prove2me | Theorems.Thm_BwSC_LowerBound_theorem_2_first_term_q0
-- name    : BwSC.LowerBound.theorem_2_first_term_q0
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T03:07:00.92602+00:00
-- url     : https://prove2.me/theorems/da6782af-30e0-492e-bd2e-2b5288c002c3
-- title:
--   Theorem 2, p. 21, first term in the phase q(S,K)=0 (S ≤ K−1): regret ≥ C/log T · (K−r)T/K
-- statement:
--   This is the first lower bound of Theorem 2 in the phase $q(S,K)=0$, i.e. for switching budgets $S\le K-1$, under the standing assumption of Appendix J.
--
--   Let $K>1$, $S\in\mathbb N$ and $T\ge 2K$ with $q(S,K)=\lfloor (S-1)/(K-1)\rfloor=0$ (with $q(0,K)=0$), so that $r(S,K)=S-1\in\{-1,0,\dots,K-2\}$, and assume the standing assumption of p. 59,
--   $$q(S,K)+2\le\log_2\log_2(T/K),\qquad\text{i.e. } T\ge 16K.$$
--   There is an absolute constant $C>0$ such that every $S$-switch policy $\pi\in\Pi_S$ admits a mean vector $\mu\in\mathbb R^K$ with $|\mu_i-\mu_j|\le1$ for all arms $i,j$ for which the unit-variance Gaussian bandit $\mathcal N(\mu_1,1),\dots,\mathcal N(\mu_K,1)$ satisfies
--   $$R^\pi_\mu(T)\ \ge\ \frac{C}{\log T}\cdot\frac{(K-r(S,K))^{2-\frac{1}{2-2^{-q(S,K)}}}}{K}\,T^{\frac{1}{2-2^{-q(S,K)}}}\ =\ \frac{C}{\log T}\cdot\frac{K-r(S,K)}{K}\,T ,$$
--   where $R^\pi_\mu(T)=T\max_i\mu_i-\mathbb E^\pi_\mu\big[\sum_{t=1}^TX_t\big]$.
--
--   This is the special case $q(S,K)=0$ of the first term of Theorem 2. It is needed separately because the proof in Appendix J (Lemmas 8, 9, 12 and eq. (46)) uses the reward gap $\Delta^{(1)}_{q+2}=-\frac{1}{2(q+2)}\sqrt{(K-r)/t^{(1)}_{q}}$, which is undefined when $q=0$ since $t^{(1)}_0=0$; the milestones for those steps are therefore stated only for $q(S,K)\ge1$. In this phase the windows of both first-class risky events start at round $1$, so the policy observes no reward of arm $k$ before the risky event is decided.
--
--   **Formalization Note** The statement has the same form as the goal theorem `BwSC.LowerBound.theorem_2` (constant chosen before $K,S,T$; `rateA` is the first rate; the class $\Pi_S$ is `IsSwitchPolicy`), restricted to $q(S,K)=0$ and to the standing assumption $q(S,K)+2\le\log_2\log_2(T/K)$ written with `Real.logb 2`.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 21, Theorem 2 (first term), case q(S,K)=0 under the standing assumption q(S,K)+2 ≤ log2 log2(T/K) of Appendix J, p. 59; App. J.3.1 (p. 65) defines Δ^(1)_{q+2} via t^(1)_q, undefined for q=0

import Mathlib
import Definitions.Def_BwSC_LowerBound_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BwSC.LowerBound
theorem theorem_2_first_term_q0 :
    ∃ C : ℝ, 0 < C ∧ ∀ (K S T : ℕ), 1 < K → 2 * K ≤ T → qIdx S K = 0 →
      (qIdx S K : ℝ) + 2 ≤ Real.logb 2 (Real.logb 2 ((T : ℝ) / K)) →
      ∀ π : BanditPolicy K, IsSwitchPolicy S T π →
        ∃ μvec : Fin K → ℝ, (∀ i j, |μvec i - μvec j| ≤ 1) ∧
          C / Real.log T * rateA K S T ≤ banditRegret (gaussianBandit μvec) π T := by sorry

end BwSC.LowerBound
