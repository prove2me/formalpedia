-- Prove2me | Theorems.Thm_BreakingSample_Conservative_lemma_1
-- name    : BreakingSample.Conservative.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:52.52242+00:00
-- url     : https://prove2.me/theorems/b39886e2-a0db-4bc7-b2a0-68c14b7cebd9
-- title:
--   Lemma 1, p. 13 — for a fixed policy, w.p. ≥ 1 − δ, ‖V̂^π − V^π‖∞ obeys the instance-dependent bound (31), itself ≤ 6√(2log(4|S|log(e/(1−γ))/δ)/(N(1−γ)³))
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\gamma)$ be a finite discounted MDP with rewards in $[0,1]$ and $\gamma\in(0,1)$, fix a deterministic policy $\pi$, let $0 < \delta < 1$, and write
--
--   $$L = \log\Big(\frac{4|\mathcal S|\log(e/(1-\gamma))}{\delta}\Big).$$
--
--   Suppose $N \ge \frac{32e^2}{1-\gamma}L$, and let $\widehat P$ be the empirical kernel built from $N$ independent samples per pair. Then with probability at least $1-\delta$, the value functions $V^\pi$ of $(P,r)$ and $\widehat V^\pi$ of $(\widehat P, r)$ obey
--
--   $$\big\|\widehat V^\pi - V^\pi\big\|_\infty \le 4\gamma\sqrt{\frac{2L}{N}}\Big\|(I-\gamma P_\pi)^{-1}\sqrt{\mathrm{Var}_{P_\pi}[V^\pi]}\Big\|_\infty + \frac{2\gamma L}{(1-\gamma)N}\|V^\pi\|_\infty \le 6\sqrt{\frac{2L}{N(1-\gamma)^3}}.$$
--
--   The first bound depends on the instance, the second is the worst case; Lemma 1 is the policy-evaluation result behind the first term of (53).
--
--   **Formalization Note** The event bounded by $\delta$ is the failure of the conjunction of the two inequalities of the chain; the second inequality does not depend on the data, so the statement also asserts it outright. No $N > 0$ is added: for nonempty $\mathcal S$ the threshold forces it.
-- source:
--   arXiv:2005.12900v8, Lemma 1, p. 13, (30)–(31)

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Sampling

namespace BreakingSample.Conservative

open Matrix

theorem lemma_1 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : BreakingSample.Perturbed.IsDiscountedMDP P r γ)
    (π : S → A) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (N : ℕ) :
    let L : ℝ := Real.log (4 * (Fintype.card S : ℝ) * Real.log (Real.exp 1 / (1 - γ)) / δ)
    32 * Real.exp 1 ^ 2 / (1 - γ) * L ≤ (N : ℝ) →
    BreakingSample.Perturbed.sampleProb P N (fun x =>
      ¬ (‖fun s => BreakingSample.Perturbed.value (BreakingSample.Perturbed.empKernel x) r γ π s - BreakingSample.Perturbed.value P r γ π s‖
            ≤ 4 * γ * Real.sqrt (2 * L / N)
                * ‖BreakingSample.Perturbed.resolvent P γ π *ᵥ (fun s => Real.sqrt (BreakingSample.Perturbed.varPi P π (BreakingSample.Perturbed.value P r γ π) s))‖
              + 2 * γ * L / ((1 - γ) * N) * ‖BreakingSample.Perturbed.value P r γ π‖ ∧
         4 * γ * Real.sqrt (2 * L / N)
                * ‖BreakingSample.Perturbed.resolvent P γ π *ᵥ (fun s => Real.sqrt (BreakingSample.Perturbed.varPi P π (BreakingSample.Perturbed.value P r γ π) s))‖
              + 2 * γ * L / ((1 - γ) * N) * ‖BreakingSample.Perturbed.value P r γ π‖
            ≤ 6 * Real.sqrt (2 * L / (N * (1 - γ) ^ 3)))) ≤ δ := by sorry

end BreakingSample.Conservative
