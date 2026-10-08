-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_sao_stochastic_regret
-- name    : BestBothWorlds.SAO.sao_stochastic_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:47:07.274026+00:00
-- url     : https://prove2.me/theorems/d1470854-8222-40fe-afb9-01285799617b
-- title:
--   Theorem 4.1 (stochastic model) — $\overline R_n\le260K(1+\log K)\log^2(\beta)/\Delta$ w.p. $1-\delta$
-- statement:
--   Let $K\ge2$ arms, $n\ge K$ rounds and $\delta\in(0,1)$, and let $\beta=10Kn^3\delta^{-1}$. Let $\nu_1,\dots,\nu_K$ be probability distributions on $[0,1]$ with means $\mu_1,\dots,\mu_K$, and suppose some arm has positive gap $\Delta_i=\max_j\mu_j-\mu_i>0$. Let $\Delta=\min_{i:\Delta_i>0}\Delta_i$. Then, in the stochastic model, with probability at least $1-\delta$, SAO with parameter $\beta$ satisfies
--   $$\overline R_n\le\frac{260K(1+\log K)\log^2(\beta)}{\Delta},$$
--   where $\overline R_n=\sum_{t=1}^n(\max_i\mu_i-\mu_{I_t})$ is the pseudo-regret.
--
--   This is the stochastic half of the main result: the same algorithm, with no knowledge of which model it faces, attains the logarithmic, gap-dependent regret of stochastic bandit algorithms.
--
--   **Formalization Note** The hypothesis that some arm has positive gap makes $\Delta$ well defined. If every arm is optimal, then $\overline R_n=0$ and there is nothing to prove.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 12, Theorem 4.1 ("More precisely" part, stochastic model)

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

open MeasureTheory

namespace BestBothWorlds.SAO

/-- Theorem 4.1, stochastic model (p. 12): for `δ ∈ (0,1)`, SAO with `β = 10Kn³δ⁻¹` satisfies,
with probability at least `1 - δ`, `R̄_n ≤ 260 K (1 + log K) log²(β)/Δ`, when some arm has a
positive gap. -/
theorem sao_stochastic_regret (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) (hgap : ∃ i, 0 < gap (mean ν) i) :
    1 - δ ≤ probStoch n (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) ν (fun _ I =>
      pseudoRegret (mean ν) I ≤
        260 * K * (1 + Real.log K) * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ^ 2 / minGap (mean ν)) := by sorry

end BestBothWorlds.SAO
