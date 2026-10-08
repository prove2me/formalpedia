-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_sao_best_of_both_worlds
-- name    : BestBothWorlds.SAO.sao_best_of_both_worlds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:47:12.01139+00:00
-- url     : https://prove2.me/theorems/1ee2be50-e871-412d-82a0-3ecce50e59c7
-- title:
--   Theorem 4.1 — SAO's high-probability regret in the stochastic and the adversarial model
-- statement:
--   Let $K\ge2$ arms, $n\ge K$ rounds and $\delta\in(0,1)$, and let $\beta=10Kn^3\delta^{-1}$. The SAO strategy with parameter $\beta$ satisfies both of the following.
--
--   1. **Stochastic model.** For all probability distributions $\nu_1,\dots,\nu_K$ on $[0,1]$ with means $\mu_i$ such that some arm has positive gap, let $\Delta=\min_{i:\Delta_i>0}\Delta_i$. With probability at least $1-\delta$,
--   $$\overline R_n\le\frac{260K(1+\log K)\log^2(\beta)}{\Delta}.$$
--   2. **Adversarial model.** For every adaptive adversary with rewards in $[0,1]$, with probability at least $1-\delta$,
--   $$R_n\le60(1+\log K)(1+\log n)\sqrt{nK\log(\beta)+5K^2\log^2(\beta)}+200K^2\log^2(\beta).$$
--
--   Here $\overline R_n=\sum_{t}(\max_i\mu_i-\mu_{I_t})$ is the pseudo-regret and $R_n=\max_i\sum_t g_{i,t}-\sum_t g_{I_t,t}$ is the regret.
--
--   A single algorithm, with no knowledge of which model it faces, achieves the logarithmic gap-dependent regret of stochastic bandits and the $\tilde O(\sqrt{nK})$ regret of adversarial bandits. This is the "best of both worlds" property.
--
--   **Formalization Note** The adversary is deterministic and adaptive ($g_t$ depends on $I_1,\dots,I_{t-1}$), which covers randomized adversaries by mixing. Probabilities are taken over SAO's internal randomization and, in the stochastic model, over the independent rewards $g_{i,t}\sim\nu_i$. The theorem's first display (expected regret in $O(\cdot)$ form with $\beta=n^4$) is not part of this statement.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 12, Theorem 4.1 ("More precisely" part)

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

open MeasureTheory

namespace BestBothWorlds.SAO

/-- Theorem 4.1, high-probability part (p. 12): for any `δ ∈ (0,1)`, with probability at least
`1 - δ`, SAO with `β = 10Kn³δ⁻¹` satisfies in the stochastic model
`R̄_n ≤ 260 K (1 + log K) log²(β)/Δ` (whenever some arm has a positive gap), and in the
adversarial model (any adaptive adversary with rewards in `[0,1]`)
`R_n ≤ 60 (1 + log K)(1 + log n) √(nK log β + 5K² log² β) + 200 K² log² β`. -/
theorem sao_best_of_both_worlds (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    (∀ (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)],
      (∀ i, ν i (Set.Icc 0 1)ᶜ = 0) → (∃ i, 0 < gap (mean ν) i) →
        1 - δ ≤ probStoch n (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) ν (fun _ I =>
          pseudoRegret (mean ν) I ≤
            260 * K * (1 + Real.log K) * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ^ 2 / minGap (mean ν))) ∧
    (∀ adv : Adversary K, adv.IsBounded →
      1 - δ ≤ probEvent n (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) adv (fun I =>
        regret adv I ≤
          60 * (1 + Real.log K) * (1 + Real.log n) *
              Real.sqrt (n * K * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) + 5 * K ^ 2 * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ^ 2) +
            200 * K ^ 2 * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ^ 2)) := by sorry

end BestBothWorlds.SAO
