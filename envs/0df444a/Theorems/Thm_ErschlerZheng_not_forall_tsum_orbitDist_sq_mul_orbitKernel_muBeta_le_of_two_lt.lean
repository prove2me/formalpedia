-- Prove2me | Theorems.Thm_ErschlerZheng_not_forall_tsum_orbitDist_sq_mul_orbitKernel_muBeta_le_of_two_lt
-- name    : ErschlerZheng.not_forall_tsum_orbitDist_sq_mul_orbitKernel_muBeta_le_of_two_lt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:16:14.840982+00:00
-- url     : https://prove2.me/theorems/367a5e77-0de2-490e-a713-d3d367dc2bad
-- title:
--   Proposition 7.18 (ii), second-moment bound, for all r > 2 fails — for some D, ω, β and A meeting the proposition's hypotheses, no constant C gives the bound for every r > 2
-- statement:
--   It is not true that for every $D$, every string $\omega$ satisfying Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), every $\beta$ with $1 - \frac1D < \beta < 1$ and every positive integer $A$ divisible by $D$, there is a constant $C$ such that for every $x$ in the orbit $1^\infty \cdot G_\omega$ (`orbitOne`) and every real $r > 2$,
--   $$\sum_{y : d(x,y) \le r} d(x,y)^2 P(x, y) \le C r^{2-\beta} (\log_2 r)^{2A(\beta-\frac1D)} (\log_2\log_2 r)^{1+\frac1D}.$$
--   Here $P$ is the transition kernel induced by $\mu_\beta$ (`muBeta`) with $k_n = A\lfloor\log_2 n\rfloor$ (`kLog A`) on the orbit (`orbitKernel … oneRay`), $d(x, y)$ is the Schreier distance (`orbitDist`), the sum over $y$ is over the orbit, and $\log_2$ is `Real.logb 2`.
--
--   This is not a result of the paper. The paper prints Proposition 7.18 with no range for $r$; the milestone `ErschlerZheng.orbitKernel_muBeta_le_and_tail_le` asserts its bounds for $r \ge 4$, and `ErschlerZheng.orbitKernel_muBeta_le_and_tail_le_of_three_le` extends them to $r \ge 3$. This statement shows that for the truncated second moment the hypothesis on $r$ cannot be weakened to $r > 2$. It backs the sentence of the note `orbitKernel_muBeta_le_and_tail_le` saying so. The statement negates the second bound of (ii) of that milestone, taken on its own and with the hypothesis $r \ge 4$ replaced by $r > 2$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 46, Proposition 7.18 (ii), the second-moment bound, for every r > 2 (fails)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem not_forall_tsum_orbitDist_sq_mul_orbitKernel_muBeta_le_of_two_lt :
    ¬ ∀ (D : ℕ) (ω : ℕ → Fin 3), SatisfiesFr D ω → ∀ β : ℝ, 1 - 1 / (D : ℝ) < β → β < 1 →
      ∀ A : ℕ, 0 < A → D ∣ A →
      ∃ C : ℝ, ∀ x : orbitOne ω, ∀ r : ℝ, 2 < r →
        ∑' y : orbitOne ω,
            (if orbitDist ω x y ≤ r then
              orbitDist ω x y ^ 2 * orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay x y
            else 0) ≤
          C * r ^ (2 - β) * Real.logb 2 r ^ (2 * (A : ℝ) * (β - 1 / (D : ℝ))) *
            Real.logb 2 (Real.logb 2 r) ^ (1 + 1 / (D : ℝ)) := by
  sorry

end ErschlerZheng
