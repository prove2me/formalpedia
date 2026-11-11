-- Prove2me | Theorems.Thm_ConsumerUtilityApprox_UnitDemand_eq_5_11
-- name    : ConsumerUtilityApprox.UnitDemand.eq_5_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:55:39.619805+00:00
-- url     : https://prove2.me/theorems/9d35cc4c-d0ee-431c-af16-84cedef9bdd8
-- title:
--   Equation (5.11) — the fair contention rule selects every requester with probability c_j ≥ 1 − 1/e
-- statement:
--   Let $Q_{kj}\in[0,1]$ be announced request probabilities with $\sum_kQ_{kj}\le1$ for every item $j$. Fix an item $j$ and a buyer $i$ who requests $j$, and let every other buyer $k$ request $j$ independently with probability $Q_{kj}$. Under the fair rule (sole requester selected; otherwise requester $i$ with probability $\frac{1}{\sum_kQ_{kj}}\big(\sum_{k\in A_j\setminus\{i\}}\frac{Q_{kj}}{|A_j|-1}+\sum_{k\notin A_j}\frac{Q_{kj}}{|A_j|}\big)$, uniformly if $\sum_kQ_{kj}=0$), the probability that $i$ is selected is
--   $$c_j=\Pr(i\text{ selected for }j\mid i\text{ requests }j)=\begin{cases}1,&\sum_kQ_{kj}=0,\\ \dfrac{1-\prod_k(1-Q_{kj})}{\sum_kQ_{kj}},&\text{otherwise,}\end{cases}\qquad c_j\ge1-\frac1e.$$
--   It holds for every buyer, including a deviating buyer whose own announced $Q_{ij}$ differs from its actual request, which is what makes equal service probabilities possible.
--
--   Differences from the source:
--   - encoding: the conditional probability Pr(i selected for j | i requests j), others requesting independently → the sum over the sets A of other requesters of ∏_{k≠i}(Q_kj or 1 − Q_kj) times fairSelProb Q j (insert i A) i; reason: the conditional law of the other requesters given i's request
-- source:
--   Goldner, Lundy, Tsilivis, A Constant-Factor Approximation to Multidimensional Consumer Utility, arXiv:2610.10516 (version of November 3, 2026, sha256 94e0dd44…), p. 26, equation (5.11) (= (C.10), Appendix C.5, pp. 49–50)

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Mechanisms
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MultiItemRev.BundlingOpt

namespace ConsumerUtilityApprox.UnitDemand

theorem eq_5_11 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (Q : Fin n → Fin m → ℝ)
    (hQ : ∀ k j, 0 ≤ Q k j ∧ Q k j ≤ 1) (hfeas : ∀ j, ∑ k, Q k j ≤ 1)
    (j : Fin m) (i : Fin n) :
    (∑ A ∈ (Finset.univ.erase i).powerset,
        (∏ k ∈ Finset.univ.erase i, if k ∈ A then Q k j else 1 - Q k j) *
          fairSelProb Q j (insert i A) i) = selectionConst Q j ∧
      1 - Real.exp (-1) ≤ selectionConst Q j := by sorry

end ConsumerUtilityApprox.UnitDemand
