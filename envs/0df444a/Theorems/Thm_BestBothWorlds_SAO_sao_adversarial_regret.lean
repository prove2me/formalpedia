-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_sao_adversarial_regret
-- name    : BestBothWorlds.SAO.sao_adversarial_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:47:29.965301+00:00
-- url     : https://prove2.me/theorems/db3f8421-1d49-4961-b999-1eaa76901c19
-- title:
--   Theorem 4.1 (adversarial model) — $R_n\le60(1+\log K)(1+\log n)\sqrt{nK\log\beta+5K^2\log^2\beta}+200K^2\log^2\beta$
-- statement:
--   Let $K\ge2$ arms, $n\ge K$ rounds and $\delta\in(0,1)$, and let $\beta=10Kn^3\delta^{-1}$. Then, against every adaptive adversary with rewards in $[0,1]$, with probability at least $1-\delta$, SAO with parameter $\beta$ satisfies
--   $$R_n\le60(1+\log K)(1+\log n)\sqrt{nK\log\beta+5K^2\log^2\beta}+200K^2\log^2\beta,$$
--   where $R_n=\max_i\sum_{t=1}^n g_{i,t}-\sum_{t=1}^n g_{I_t,t}$ is the regret, computed with the rewards the adversary produces along the run.
--
--   This is the adversarial half of the main result: up to logarithmic factors, SAO matches the $\sqrt{nK}$ minimax regret against adaptive adversaries.
--
--   **Formalization Note** The adversary is deterministic and adaptive: $g_t$ is a function of $I_1,\dots,I_{t-1}$. A randomized adversary is a mixture of deterministic ones, and the bound holds uniformly over deterministic adversaries.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 12, Theorem 4.1 ("More precisely" part, adversarial model)

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

open MeasureTheory

namespace BestBothWorlds.SAO

/-- Theorem 4.1, adversarial model (p. 12): for `δ ∈ (0,1)`, SAO with `β = 10Kn³δ⁻¹` satisfies,
against every adaptive adversary with rewards in `[0,1]`, with probability at least `1 - δ`,
`R_n ≤ 60 (1 + log K)(1 + log n) √(nK log β + 5K² log² β) + 200 K² log² β`. -/
theorem sao_adversarial_regret (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (adv : Adversary K) (hadv : adv.IsBounded) :
    1 - δ ≤ probEvent n (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) adv (fun I =>
      regret adv I ≤
        60 * (1 + Real.log K) * (1 + Real.log n) *
            Real.sqrt (n * K * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) + 5 * K ^ 2 * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ^ 2) +
          200 * K ^ 2 * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ^ 2) := by sorry

end BestBothWorlds.SAO
