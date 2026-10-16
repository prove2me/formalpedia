-- Prove2me | Theorems.Thm_BreakingSample_PolicyEval_lemma_1
-- name    : BreakingSample.PolicyEval.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:41.095257+00:00
-- url     : https://prove2.me/theorems/3711fae6-d476-4aec-8ca2-008c390e6f58
-- title:
--   Lemma 1, p. 13 — for a fixed π and N ≥ (32e²/(1−γ))log(4|S|log(e/(1−γ))/δ), w.p. ≥ 1 − δ, the instance-dependent and worst-case bounds (31) on ‖V̂^π − V^π‖∞
-- statement:
--   Let $(P,r,\gamma)$ be a discounted MDP in the standing setting (finite states and actions, $P$ a transition kernel, $r\in[0,1]$, $0<\gamma<1$) and fix a deterministic policy $\pi$, independent of the data. Let $0<\delta<1$, put
--   $$
--   L=\log\Big(\frac{4|\mathcal S|\log\big(\frac{e}{1-\gamma}\big)}{\delta}\Big),
--   $$
--   and suppose $N\ge\frac{32e^2}{1-\gamma}L$. Let $\widehat P$ be the empirical kernel built from $N$ samples per state-action pair, $V^\pi=(I-\gamma P_\pi)^{-1}r_\pi$ the true value of $\pi$ and $\widehat V^\pi=(I-\gamma\widehat P_\pi)^{-1}r_\pi$ its plug-in estimate. Then with probability at least $1-\delta$,
--   $$
--   \big\|\widehat V^\pi-V^\pi\big\|_\infty\le4\gamma\sqrt{\frac{2L}{N}}\Big\|(I-\gamma P_\pi)^{-1}\sqrt{\mathrm{Var}_{P_\pi}[V^\pi]}\Big\|_\infty+\frac{2\gamma L}{(1-\gamma)N}\|V^\pi\|_\infty\le6\sqrt{\frac{2L}{N(1-\gamma)^3}} .
--   $$
--
--   The first bound depends on the instance through $P_\pi$ and $V^\pi$; the second is the worst-case rate, from which Theorem 3 follows.
--
--   **Formalization Note** The chain is stated as two inequalities inside the event: the estimation error is at most the middle expression, and the middle expression is at most the right-hand side. $\widehat V^\pi$ is the value function of $\pi$ under the empirical kernel, equal to the matrix form by (27). The same lemma is posed in the sibling missions 1 and 2 of this paper series.
-- source:
--   arXiv:2005.12900v8, Lemma 1, (30)–(31), §6.2, p. 13

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Sampling

namespace BreakingSample.PolicyEval

open Matrix

/-- Lemma 1 and (31), arXiv:2005.12900v8, §6.2, p. 13: for a fixed policy `π`, `0 < δ < 1` and
`N ≥ 32e²/(1−γ) · L` with `L = log(4|S| log(e/(1−γ))/δ)`, with probability at least `1 − δ` the
plug-in estimate `V̂^π` (the value of `π` in the empirical MDP) obeys both inequalities of (31). -/
theorem lemma_1 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
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

end BreakingSample.PolicyEval
