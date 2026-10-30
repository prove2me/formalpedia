-- Prove2me | Theorems.Thm_BwSC_LowerBound_theorem_2
-- name    : BwSC.LowerBound.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:05.315108+00:00
-- url     : https://prove2.me/theorems/122c93c4-9391-440f-b70f-e6024a91429d
-- title:
--   Theorem 2, p. 21 — every S-switch policy has regret ≥ C/log T · max{(K−r)^{2−1/(2−2^{−q})}T^{1/(2−2^{−q})}/K, K^{1−1/(2−2^{−q−1})}T^{1/(2−2^{−q−1})}}
-- statement:
--   There exists an absolute constant $C>0$ such that for all $K>1$, all budgets $S\in\mathbb N$, all horizons $T\ge2K$ and every $S$-switch policy $\pi\in\Pi_S$, there is a mean vector $\mu\in\mathbb R^K$ with $|\mu_i-\mu_j|\le1$ for all arms $i,j$ such that the unit-variance Gaussian bandit $\mathcal N(\mu_1,1),\dots,\mathcal N(\mu_K,1)$ satisfies
--   $$R^\pi_\mu(T)\ \ge\ \frac{C}{\log T}\cdot\max\left\{\frac{(K-r(S,K))^{2-\frac{1}{2-2^{-q(S,K)}}}}{K}\,T^{\frac{1}{2-2^{-q(S,K)}}},\ K^{1-\frac{1}{2-2^{-q(S,K)-1}}}\,T^{\frac{1}{2-2^{-q(S,K)-1}}}\right\},$$
--   where $q(S,K)=\lfloor (S-1)/(K-1)\rfloor$ (with $q(0,K)=0$), $r(S,K)=S-1-q(S,K)(K-1)$ (so $r=(S-1)\%(K-1)$ for $S\ge1$ and $r(0,K)=-1$), and $R^\pi_\mu(T)=T\max_i\mu_i-\mathbb E^\pi_\mu\big[\sum_{t=1}^TX_t\big]$.
--
--   This is the algorithm-independent lower bound of the paper: with the AdaLS upper bound (Theorem 1) it characterizes the optimal regret of the unit-switching-cost problem up to logarithmic factors, including the phase transitions in $S$ at multiples of $K-1$.
--
--   **Formalization Note** The paper writes $R^\pi(K,T)=\sup_{\mathcal D}R^\pi_{\mathcal D}(T)$ over standardized sub-Gaussian environments with mean spread in $[0,1]$; exhibiting one admissible Gaussian instance whose regret is at least the bound implies the paper's statement. The class $\Pi_S$ requires the budget almost surely only under unit-variance Gaussian environments, a weaker requirement than Definition 1, so the statement quantifies over at least the paper's policies. The constant $C$ is chosen before $K,S,T$: it is absolute. $\log$ is the natural logarithm; $T\ge2K\ge4$ makes $\log T>0$.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 21, Theorem 2 (proof Appendix J, pp. 59–75)

import Mathlib
import Definitions.Def_BwSC_LowerBound_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BwSC.LowerBound

/-- Theorem 2, p. 21: there is an absolute constant `C > 0` such that for all `K > 1`, `S ≥ 0`,
`T ≥ 2K` and every `S`-switch policy `π`, some unit-variance Gaussian instance with mean spread
at most `1` has regret at least `C / log T · max{A, B}`. -/
theorem theorem_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (K S T : ℕ), 1 < K → 2 * K ≤ T →
      ∀ π : BanditPolicy K, IsSwitchPolicy S T π →
        ∃ μvec : Fin K → ℝ, (∀ i j, |μvec i - μvec j| ≤ 1) ∧
          C / Real.log T * max (rateA K S T) (rateB K S T) ≤
            banditRegret (gaussianBandit μvec) π T := by sorry

end BwSC.LowerBound
