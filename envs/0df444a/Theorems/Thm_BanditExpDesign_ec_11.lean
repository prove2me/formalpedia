-- Prove2me | Theorems.Thm_BanditExpDesign_ec_11
-- name    : BanditExpDesign.ec_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:33.350257+00:00
-- url     : https://prove2.me/theorems/63fa3eca-e589-4710-99f4-2426c2274fbc
-- title:
--   (EC.11) — conditional second moments are at most $\sum_t(1/\pi_t(i)+1/\pi_t(j))$
-- statement:
--   Let $K\ge2$, $\alpha\in[0,1]$ and $\delta\in(0,2/e)$, and run EXP3EG (Algorithm 2) with these inputs. Suppose the rewards lie in $[-1,1]$. For every horizon $n$ and $i\ne j$, almost surely,
--   $$\sum_{t=1}^n\mathbb E\Big[\Big(\frac{R_t}{\pi_t(i)}\mathbb I_{A_t=i}-\frac{R_t}{\pi_t(j)}\mathbb I_{A_t=j}-\Delta^{(i,j)}\Big)^2\,\Big|\,\mathcal H_{t-1}\Big]\le\sum_{t=1}^n\frac1{\pi_t(i)}+\frac1{\pi_t(j)}.$$
--
--   The predictable quadratic variation of the treatment-effect martingale is therefore bounded by the variance proxy.
--
--   Differences from the source:
--   - reading: the display chain (EC.11), whose middle line subtracts t(Δ^{(i,j)})² → its outer inequality; reason: the sum to n subtracts n(Δ^{(i,j)})², so the printed middle line has a typo; the outer inequality is what the proof uses
--   - encoding: E[· | ℋ_{t−1}] → Mathlib condExp, so the inequality holds almost surely; reason: conditional expectations are defined up to null sets
--   - reading: R̂^max_t is the maximum over all arms (p.13) → R̂^max_t is the maximum over the active set 𝒜_t; reason: the printed rule can empty 𝒜_t and leave π_t undefined; the proofs of the paper, (EC.9)–(EC.10), use the active-set maximum, and the two rules agree while all arms are active
--   - encoding: ε_0 is used at t = 1 and not defined → ε_0 = 0; reason: R̂_0 = 0, so π_1 = 1/K for every value of ε_0; Algorithm 1 sets the same value
--   - encoding: the table of rewards r_t(a), a ∈ [K], of p.3 → the published canonical law banditMeasure of the observed history; reason: every quantity is a function of (A_s, R_s), s ≤ t, whose law under the paper's model is the canonical one; the joint law of the rewards of different arms never matters
--   - encoding: arms {1, …, K}; natural log written log or ln; t^α → Fin K; Real.log; Real.rpow; reason: Lean conventions; same instances
--   - generalization: instances of the feasible set E₀ (|Δ^{(i,j)}| = Θ(1) for all i ≠ j, p.4) → every instance with rewards in [−1,1]; reason: the statement and its proof never use the size of the gaps; E₀ is a subset, so the Lean statement specializes to the page on it
-- source:
--   Simchi-Levi–Wang, Multi-armed Bandit Experimental Design, SSRN 4224969, proof of Theorem 7, eq. (EC.11), p.ec12

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_BanditPolicy
import Definitions.Def_BanditExpDesign_EXP3EG

set_option autoImplicit false
open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BanditExpDesign

/-- **(EC.11)**, Simchi-Levi–Wang, *Multi-armed Bandit Experimental Design*, SSRN 4224969,
proof of Theorem 7, p.ec12 (outer inequality):
`∑_{t=1}^n E[((R_t/π_t(i)) 𝟙{A_t=i} - (R_t/π_t(j)) 𝟙{A_t=j} - Δ^{(i,j)})² | ℋ_{t-1}]
≤ ∑_{t=1}^n (1/π_t(i) + 1/π_t(j))`.

**Formalization Note.** Under the law of `n` rounds; `s : Fin n` is round `t = s + 1`, and
`historyFiltration K n s` is `ℋ_{t-1}`. The conditional expectations are Mathlib's `condExp`, so
the inequality holds almost surely. The printed middle line, whose `t(Δ)²` should be `n(Δ)²`, is
not part of the statement. -/
theorem ec_11 {K : ℕ} [NeZero K] (hK : 2 ≤ K) {α δ : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hδ0 : 0 < δ) (hδ : δ < 2 / Real.exp 1) (ν : StochasticBandit K) (hν : RewardsBounded ν)
    (n : ℕ) (i j : Fin K) (hij : i ≠ j) :
    ∀ᵐ h ∂(banditMeasure ν (exp3eg K α δ hα) n),
      ∑ s : Fin n,
        ((banditMeasure ν (exp3eg K α δ hα) n)[
          fun h' => (ipwDifference α δ h' s i j - ate ν i j) ^ 2 |
            historyFiltration K n (s : ℕ)]) h ≤
        varianceProxy α δ h n i j := by sorry

end BanditExpDesign
