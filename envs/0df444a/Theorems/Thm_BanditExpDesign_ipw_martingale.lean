-- Prove2me | Theorems.Thm_BanditExpDesign_ipw_martingale
-- name    : BanditExpDesign.ipw_martingale
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:26.266233+00:00
-- url     : https://prove2.me/theorems/ba87f081-e896-4727-ad7a-cede588ec682
-- title:
--   Proof of Theorem 6, p.ec10 — $M^a_t=\hat R_t(a)-t\mu_a$ is a martingale
-- statement:
--   Let $K\ge2$, $\alpha\in[0,1]$ and $\delta\in(0,2/e)$, and run EXP3EG (Algorithm 2) with these inputs. Suppose the rewards lie in $[-1,1]$. For every horizon $n$ and arm $a$, the process
--   $$M^a_t=\hat R_t(a)-t\mu_a,\qquad t\in[n],$$
--   is a martingale with respect to the history filtration $(\mathcal H_t)$ under the law of the first $n$ rounds.
--
--   The inverse-propensity weights make each increment conditionally centred, whatever the adaptive allocation.
--
--   **Formalization Note** Mathlib's `Martingale` is indexed by all of $\mathbb N$, so the process is stopped at $n$: the index is $\min(t,n)$.
--
--   Differences from the source:
--   - generalization: the proof of Theorem 6 runs with δ = 1/(2n²) → every δ ∈ (0, 2/e); reason: 1/(2n²) ≤ 1/2 < 2/e, so this contains the page's case; Theorem 7 uses the fact for this range of δ
--   - encoding: t ∈ [n] → index min(t, n) for t ∈ ℕ; reason: Mathlib martingales are indexed by ℕ; the stopped process agrees on t ≤ n
--   - reading: R̂^max_t is the maximum over all arms (p.13) → R̂^max_t is the maximum over the active set 𝒜_t; reason: the printed rule can empty 𝒜_t and leave π_t undefined; the proofs of the paper, (EC.9)–(EC.10), use the active-set maximum, and the two rules agree while all arms are active
--   - encoding: ε_0 is used at t = 1 and not defined → ε_0 = 0; reason: R̂_0 = 0, so π_1 = 1/K for every value of ε_0; Algorithm 1 sets the same value
--   - encoding: the table of rewards r_t(a), a ∈ [K], of p.3 → the published canonical law banditMeasure of the observed history; reason: every quantity is a function of (A_s, R_s), s ≤ t, whose law under the paper's model is the canonical one; the joint law of the rewards of different arms never matters
--   - encoding: arms {1, …, K}; natural log written log or ln; t^α → Fin K; Real.log; Real.rpow; reason: Lean conventions; same instances
--   - generalization: instances of the feasible set E₀ (|Δ^{(i,j)}| = Θ(1) for all i ≠ j, p.4) → every instance with rewards in [−1,1]; reason: the statement and its proof never use the size of the gaps; E₀ is a subset, so the Lean statement specializes to the page on it
-- source:
--   Simchi-Levi–Wang, Multi-armed Bandit Experimental Design, SSRN 4224969, proof of Theorem 6, first line, p.ec10

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_BanditPolicy
import Definitions.Def_BanditExpDesign_EXP3EG

set_option autoImplicit false
open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BanditExpDesign

/-- **The IPW martingale**, Simchi-Levi–Wang, *Multi-armed Bandit Experimental Design*,
SSRN 4224969, proof of Theorem 6, p.ec10: `M_t^a = R̂_t(a) - t μ_a`, `t ∈ [n]`, is a martingale.

**Formalization Note.** The space is the law `banditMeasure` of `n` rounds of EXP3EG with the
history filtration `historyFiltration K n`. Mathlib's `Martingale` is indexed by all of `ℕ`, so the
process is stopped at the horizon: `min t n`. The rewards lie in `[-1,1]` (`RewardsBounded`). -/
theorem ipw_martingale {K : ℕ} [NeZero K] (hK : 2 ≤ K) {α δ : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hδ0 : 0 < δ) (hδ : δ < 2 / Real.exp 1) (ν : StochasticBandit K) (hν : RewardsBounded ν)
    (n : ℕ) (a : Fin K) :
    Martingale
      (fun (t : ℕ) (h : BanditHistory K n) =>
        ipwEstimate α δ h (min t n) a - ((min t n : ℕ) : ℝ) * banditArmMean ν a)
      (historyFiltration K n) (banditMeasure ν (exp3eg K α δ hα) n) := by sorry

end BanditExpDesign
