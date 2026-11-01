-- Prove2me | Theorems.Thm_BanditExpDesign_unbiased
-- name    : BanditExpDesign.unbiased
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:11.583202+00:00
-- url     : https://prove2.me/theorems/7f82e064-5019-4706-8030-e745b2e0cabe
-- title:
--   §3, p.18 — unbiasedness: $\mathbb E[\hat\Delta^{(i,j)}_t]=\Delta^{(i,j)}$
-- statement:
--   Let $K\ge2$, $\alpha\in[0,1]$ and any real $\delta$, and run EXP3EG (Algorithm 2) with these inputs. Suppose the rewards lie in $[-1,1]$. For all $i\ne j$ and every $t\ge1$, the estimate $\hat\Delta_t^{(i,j)}$ is integrable and
--   $$\mathbb E[\hat\Delta_t^{(i,j)}]=\Delta^{(i,j)}.$$
--
--   The estimate stays unbiased although the arms are allocated adaptively.
--
--   Differences from the source:
--   - generalization: E[Δ̂_n] at the horizon n → every t ≥ 1; reason: contains t = n; the run up to t does not depend on n
--   - encoding: the expectation E → integrability as a conjunct, then the Bochner integral; reason: rules out the junk value 0 of a non-integrable integrand; the integrand is bounded a.s.
--   - reading: M_t^{(i,j)} = t(Δ̂_n^{(i,j)} − Δ^{(i,j)}) → M_t^{(i,j)} = t(Δ̂_t^{(i,j)} − Δ^{(i,j)}); reason: the printed index n is a typo: the martingale at time t uses the estimate at time t
--   - reading: R̂^max_t is the maximum over all arms (p.13) → R̂^max_t is the maximum over the active set 𝒜_t; reason: the printed rule can empty 𝒜_t and leave π_t undefined; the proofs of the paper, (EC.9)–(EC.10), use the active-set maximum, and the two rules agree while all arms are active
--   - encoding: ε_0 is used at t = 1 and not defined → ε_0 = 0; reason: R̂_0 = 0, so π_1 = 1/K for every value of ε_0; Algorithm 1 sets the same value
--   - encoding: the table of rewards r_t(a), a ∈ [K], of p.3 → the published canonical law banditMeasure of the observed history; reason: every quantity is a function of (A_s, R_s), s ≤ t, whose law under the paper's model is the canonical one; the joint law of the rewards of different arms never matters
--   - encoding: arms {1, …, K}; natural log written log or ln; t^α → Fin K; Real.log; Real.rpow; reason: Lean conventions; same instances
--   - generalization: EXP3EG run with its input δ (Theorem 6: δ = 1/(2n²); Theorem 7: δ < 2/e) → every real δ; reason: the propensities are positive for every δ, which is all unbiasedness uses; the page’s values of δ are special cases
--   - generalization: instances of the feasible set E₀ (|Δ^{(i,j)}| = Θ(1) for all i ≠ j, p.4) → every instance with rewards in [−1,1]; reason: the statement and its proof never use the size of the gaps; E₀ is a subset, so the Lean statement specializes to the page on it
-- source:
--   Simchi-Levi–Wang, Multi-armed Bandit Experimental Design, SSRN 4224969, §3, before Theorem 7, p.18

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_BanditPolicy
import Definitions.Def_BanditExpDesign_EXP3EG

set_option autoImplicit false
open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BanditExpDesign

/-- **Unbiasedness**, Simchi-Levi–Wang, *Multi-armed Bandit Experimental Design*, SSRN 4224969,
§3, p.18: `E[Δ̂_t^{(i,j)}] = Δ^{(i,j)}`.

**Formalization Note.** Stated for every `t ≥ 1` under the law of the first `t` rounds; the page
has `n` for the horizon. The rewards lie in `[-1,1]`, and integrability of the estimate is part of
the conclusion, so the Bochner integral is a genuine expectation. `δ` is any real number: the
propensities are positive for every input `δ`. -/
theorem unbiased {K : ℕ} [NeZero K] (hK : 2 ≤ K) {α δ : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit K) (hν : RewardsBounded ν)
    (i j : Fin K) (hij : i ≠ j) (t : ℕ) (ht : 1 ≤ t) :
    Integrable (fun h => ateEstimate α δ h t i j) (banditMeasure ν (exp3eg K α δ hα) t) ∧
      ∫ h, ateEstimate α δ h t i j ∂(banditMeasure ν (exp3eg K α δ hα) t) = ate ν i j := by sorry

end BanditExpDesign
