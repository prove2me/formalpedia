-- Prove2me | Theorems.Thm_BanditExpDesign_theorem_7
-- name    : BanditExpDesign.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:25.933029+00:00
-- url     : https://prove2.me/theorems/126041fd-d717-4083-a04f-822a6e0d49ba
-- title:
--   Theorem 7 — EXP3EG estimates every treatment effect within $4(2+2K^2(1+e^2))\log(2/\delta)/\sqrt{t^{1-\alpha}}$ with probability $1-\delta$ (corrected: for each $t$, not uniformly in $t$)
-- statement:
--   Run EXP3EG with $\alpha\in[0,1]$ on $K\ge2$ arms with rewards in $[-1,1]$, and let $\hat\Delta_t^{(i,j)}$ be its inverse-propensity-weighted estimate of the treatment effect $\Delta^{(i,j)}=\mu_i-\mu_j$.
--
--   1. For $\delta\in(0,2/e)$, all $i\ne j$ and every $t\ge1$, with probability at least $1-\delta$,
--   $$\big|\hat\Delta_t^{(i,j)}-\Delta^{(i,j)}\big|\le\frac{4(2+2K^2(1+e^2))\log(2/\delta)}{\sqrt{t^{1-\alpha}}}.$$
--   2. There is a constant $c$, depending only on $K$, such that for every horizon $n\ge1$, every $\alpha\in[0,1]$, every such instance and all $i<j$, EXP3EG run with $\delta=1/(2n^2)$ has
--   $$e(n,\hat\Delta^{(i,j)})=\mathbb E\big|\hat\Delta_n^{(i,j)}-\Delta^{(i,j)}\big|\le\frac c{\sqrt{n^{1-\alpha}}}.$$
--
--   This is the finite-sample inference guarantee of the design: the parameter $\alpha$ trades regret $\tilde O(n^{1-\alpha})$ against estimation error $O(1/\sqrt{n^{1-\alpha}})$, for every instance and every pair of arms.
--
--   **Formalization Note** Clause 2 does not follow by integrating clause 1, which leaves a factor $\log n$. Its integrand is shown integrable as part of the statement. Quantifying over $i<j$ is the page's $\max_{i<j\le K}$ unfolded. The constant $c$ is chosen after $K$ and before $n$, $\alpha$ and the instance.
--
--   Differences from the source:
--   - correction: with probability at least 1 − δ, for all t ∈ [n] (one event) → for every t, with probability at least 1 − δ; reason: the printed uniform claim is false: K = 2, α = 0, δ = 1/2, arms ±1 with means ±1/2; every π_t(a) ∈ [1/C′, 1], the increments are bounded with conditional variance at least 3, and by the martingale law of the iterated logarithm (11) fails infinitely often almost surely, so the probability that it holds for all t ≤ n tends to 0
--   - generalization: t ∈ [n] → every t ≥ 1; reason: contains every t ∈ [n] for every n; the run up to t depends on n only through δ, which is a free input here
--   - reading: max_{i<j≤K} e(n, Δ̂_n^{(i,j)}) = O(1/√(n^{1−α})) → ∃ c depending only on K, for all n, α and instances, for all i < j: e(n, Δ̂^{(i,j)}) ≤ c/√(n^{1−α}); reason: the strongest content the O(·) can have; c cannot be independent of K
--   - encoding: the expectation in e(n, Δ̂) → integrability as a conjunct, then the Bochner integral; reason: rules out the junk value 0 of a non-integrable integrand; the integrand is bounded a.s.
--   - encoding: for any fixed i ≠ j ∈ [k] → i ≠ j in Fin K; reason: [k] is a typo for [K]
--   - reading: R̂^max_t is the maximum over all arms (p.13) → R̂^max_t is the maximum over the active set 𝒜_t; reason: the printed rule can empty 𝒜_t and leave π_t undefined; the proofs of the paper, (EC.9)–(EC.10), use the active-set maximum, and the two rules agree while all arms are active
--   - encoding: ε_0 is used at t = 1 and not defined → ε_0 = 0; reason: R̂_0 = 0, so π_1 = 1/K for every value of ε_0; Algorithm 1 sets the same value
--   - encoding: the table of rewards r_t(a), a ∈ [K], of p.3 → the published canonical law banditMeasure of the observed history; reason: every quantity is a function of (A_s, R_s), s ≤ t, whose law under the paper's model is the canonical one; the joint law of the rewards of different arms never matters
--   - encoding: arms {1, …, K}; natural log written log or ln; t^α → Fin K; Real.log; Real.rpow; reason: Lean conventions; same instances
--   - encoding: δ < 2/e → 0 < δ < 2/e; reason: δ is a probability level; for δ ≤ 0 the bound 1 − δ > 1 and log(2/δ) are meaningless, so only undefined cases are excluded
--   - generalization: instances of the feasible set E₀ (|Δ^{(i,j)}| = Θ(1) for all i ≠ j, p.4) → every instance with rewards in [−1,1]; reason: the statement and its proof never use the size of the gaps; E₀ is a subset, so the Lean statement specializes to the page on it
-- source:
--   Simchi-Levi–Wang, Multi-armed Bandit Experimental Design, SSRN 4224969, Theorem 7, eq. (11), p.18

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_BanditPolicy
import Definitions.Def_BanditExpDesign_EXP3EG

set_option autoImplicit false
open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BanditExpDesign

/-- **Theorem 7** (corrected: for each `t`, not uniformly in `t`), Simchi-Levi–Wang,
*Multi-armed Bandit Experimental Design*, SSRN 4224969, p.18, eq. (11). Run EXP3EG with
`α ∈ [0,1]` on `K ≥ 2` arms with rewards in `[-1,1]`.

1. For `δ ∈ (0, 2/e)`, `i ≠ j` and every `t ≥ 1`, with probability at least `1 - δ`,
   `|Δ̂_t^{(i,j)} - Δ^{(i,j)}| ≤ 4(2 + 2K²(1+e²)) log(2/δ) / √(t^{1-α})`.
2. There is a constant `c`, depending only on `K`, such that for every horizon `n ≥ 1`, EXP3EG run
   with `δ = 1/(2n²)` has `e(n, Δ̂^{(i,j)}) ≤ c/√(n^{1-α})` for all `i < j`, for every `α ∈ [0,1]` and
   every instance. This is `max_{i<j≤K} e(n, Δ̂_n^{(i,j)}) = O(1/√(n^{1-α}))`.

**Formalization Note.** The printed "with probability at least `1 - δ`, for all `t ∈ [n]`" is false
uniformly in `t` (law of the iterated logarithm), so "for every `t`" sits outside the probability.
The law of the first `t` rounds is `banditMeasure`; the run up to `t` does not depend on the horizon.
`∀ i < j` is the `max` of the page unfolded. `c` is chosen after `K` and before `n`, `α`, `ν`.
Integrability in clause 2 makes `estimationError` a genuine expectation. The logarithm is natural
and `t ^ (1 - α)` is `Real.rpow`. -/
theorem theorem_7 {K : ℕ} [NeZero K] (hK : 2 ≤ K) :
    (∀ (α δ : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1), 0 < δ → δ < 2 / Real.exp 1 →
      ∀ ν : StochasticBandit K, RewardsBounded ν → ∀ i j : Fin K, i ≠ j →
        ∀ t : ℕ, 1 ≤ t →
          1 - δ ≤ (banditMeasure ν (exp3eg K α δ hα) t).real
            {h | |ateEstimate α δ h t i j - ate ν i j| ≤
              4 * (2 + 2 * (K : ℝ) ^ 2 * (1 + Real.exp 1 ^ 2)) * Real.log (2 / δ) /
                Real.sqrt ((t : ℝ) ^ (1 - α))}) ∧
    (∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1),
      ∀ ν : StochasticBandit K, RewardsBounded ν → ∀ i j : Fin K, i < j →
        Integrable (fun h => |ateEstimate α (1 / (2 * (n : ℝ) ^ 2)) h n i j - ate ν i j|)
            (banditMeasure ν (exp3eg K α (1 / (2 * (n : ℝ) ^ 2)) hα) n) ∧
          estimationError ν (exp3eg K α (1 / (2 * (n : ℝ) ^ 2)) hα) n
              (fun h => ateEstimate α (1 / (2 * (n : ℝ) ^ 2)) h n i j) i j ≤
            c / Real.sqrt ((n : ℝ) ^ (1 - α))) := by sorry

end BanditExpDesign
