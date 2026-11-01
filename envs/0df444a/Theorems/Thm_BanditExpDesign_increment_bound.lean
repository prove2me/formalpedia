-- Prove2me | Theorems.Thm_BanditExpDesign_increment_bound
-- name    : BanditExpDesign.increment_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:12.892519+00:00
-- url     : https://prove2.me/theorems/8a6f8dcd-6797-4b6f-a2a8-d9116e491dc8
-- title:
--   Proof of Theorem 7, first display, p.ec12 — $|M^{(i,j)}_t-M^{(i,j)}_{t-1}|\le2+1/\pi_t(i)+1/\pi_t(j)$
-- statement:
--   Let $K\ge2$, $\alpha\in[0,1]$ and $\delta\in(0,2/e)$, and run EXP3EG (Algorithm 2) with these inputs. Suppose the reward laws are carried by $[-1,1]$. Along every history, if $|R_t|\le1$ in round $t$ then, for $i\ne j$,
--   $$\big|M_t^{(i,j)}-M_{t-1}^{(i,j)}\big|=\Big|\frac{R_t}{\pi_t(i)}\mathbb I_{A_t=i}-\frac{R_t}{\pi_t(j)}\mathbb I_{A_t=j}-(\mu_i-\mu_j)\Big|\le2+\frac1{\pi_t(i)}+\frac1{\pi_t(j)}.$$
--
--   This is the almost-sure bound on the increments that Bernstein's inequality needs.
--
--   **Formalization Note** The statement is pathwise, for a history $h$ of $n$ rounds and round $t=s+1\le n$; $|R_t|\le1$ is a hypothesis on the path, and it holds almost surely under the law of the run.
--
--   Differences from the source:
--   - encoding: |R_t| ≤ 1 from the model → a hypothesis on the round of the path; reason: the claim is pathwise and the model gives the hypothesis almost surely
--   - reading: R̂^max_t is the maximum over all arms (p.13) → R̂^max_t is the maximum over the active set 𝒜_t; reason: the printed rule can empty 𝒜_t and leave π_t undefined; the proofs of the paper, (EC.9)–(EC.10), use the active-set maximum, and the two rules agree while all arms are active
--   - encoding: ε_0 is used at t = 1 and not defined → ε_0 = 0; reason: R̂_0 = 0, so π_1 = 1/K for every value of ε_0; Algorithm 1 sets the same value
--   - encoding: arms {1, …, K}; natural log written log or ln; t^α → Fin K; Real.log; Real.rpow; reason: Lean conventions; same instances
--   - generalization: instances of the feasible set E₀ (|Δ^{(i,j)}| = Θ(1) for all i ≠ j, p.4) → every instance with rewards in [−1,1]; reason: the statement and its proof never use the size of the gaps; E₀ is a subset, so the Lean statement specializes to the page on it
-- source:
--   Simchi-Levi–Wang, Multi-armed Bandit Experimental Design, SSRN 4224969, proof of Theorem 7, first display, p.ec12

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_BanditPolicy
import Definitions.Def_BanditExpDesign_EXP3EG

set_option autoImplicit false
open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BanditExpDesign

/-- **The increment bound**, Simchi-Levi–Wang, *Multi-armed Bandit Experimental Design*,
SSRN 4224969, proof of Theorem 7, first display, p.ec12:
`|M_t^{(i,j)} - M_{t-1}^{(i,j)}| = |(R_t/π_t(i)) 𝟙{A_t=i} - (R_t/π_t(j)) 𝟙{A_t=j} - (μ_i - μ_j)|
≤ 2 + 1/π_t(i) + 1/π_t(j)`.

**Formalization Note.** Pathwise, for round `t = s + 1` of a history `h` whose reward of that round
satisfies `|R_t| ≤ 1`. `RewardsBounded ν` gives `|μ_i|, |μ_j| ≤ 1`. -/
theorem increment_bound {K : ℕ} [NeZero K] (hK : 2 ≤ K) {α δ : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hδ0 : 0 < δ) (hδ : δ < 2 / Real.exp 1)
    (ν : StochasticBandit K) (hν : RewardsBounded ν) {n : ℕ} (h : BanditHistory K n) (s : Fin n)
    (i j : Fin K) (hij : i ≠ j) (hR : |(h s).2| ≤ 1) :
    |ateMartingale ν α δ h ((s : ℕ) + 1) i j - ateMartingale ν α δ h (s : ℕ) i j| =
        |ipwDifference α δ h s i j - ate ν i j| ∧
      |ipwDifference α δ h s i j - ate ν i j| ≤
        2 + 1 / propensity α δ h ((s : ℕ) + 1) i + 1 / propensity α δ h ((s : ℕ) + 1) j := by sorry

end BanditExpDesign
