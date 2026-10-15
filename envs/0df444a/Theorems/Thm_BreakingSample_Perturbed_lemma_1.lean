-- Prove2me | Theorems.Thm_BreakingSample_Perturbed_lemma_1
-- name    : BreakingSample.Perturbed.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:05.88199+00:00
-- url     : https://prove2.me/theorems/d79fcf0e-1ded-4c33-add2-95bde9ba0271
-- title:
--   Lemma 1 — fixed-policy empirical value bound
-- statement:
--   Fix a deterministic policy $\pi$ before drawing $N$ independent next-state samples per state-action pair. For $0<\delta<1$ and $N\ge 32e^2\log(4|S|\log(e/(1-\gamma))/\delta)/(1-\gamma)$, with probability at least $1-\delta$ the empirical and true values satisfy the chain of inequalities in display (31): $\|\widehat V^\pi-V^\pi\|_\infty$ is at most the instance-dependent bound $4\gamma\sqrt{2\log(4|S|\log(e/(1-\gamma))/\delta)/N}\,\|(I-\gamma P_\pi)^{-1}\sqrt{\operatorname{Var}_{P_\pi}(V^\pi)}\|_\infty+\frac{2\gamma\log(4|S|\log(e/(1-\gamma))/\delta)}{(1-\gamma)N}\|V^\pi\|_\infty$, which is in turn at most the worst-case bound, so in particular
--
--   $$\|\widehat V^\pi-V^\pi\|_\infty\le 6\sqrt{\frac{2\log(4|S|\log(e/(1-\gamma))/\delta)}{N(1-\gamma)^3}}.$$
--
--   The two inequalities provide fixed-policy concentration for the later planning analysis.
--
--   **Formalization Note** The finite sample probability is expressed as a failure-event bound. The state set is nonempty so the cardinality in the logarithm is positive.
-- source:
--   arXiv:2005.12900v8, Lemma 1, (30)–(31), p. 13

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Sampling

namespace BreakingSample.Perturbed

/-- Lemma 1 and (31), arXiv:2005.12900v8, p. 13: the chain `‖V̂^π − V^π‖∞ ≤ (instance-dependent bound) ≤ 6√(…)`,
both links as printed. -/
theorem lemma_1 {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A)
    (δ : ℝ) (N : ℕ) (hM : IsDiscountedMDP P r γ) (hδ : 0 < δ ∧ δ < 1)
    (hN : 32 * (Real.exp 1) ^ 2 / (1 - γ) *
      Real.log (4 * Fintype.card S * Real.log (Real.exp 1 / (1 - γ)) / δ) ≤ (N : ℝ)) :
    sampleProb P N (fun x => ¬
      (‖(fun s => value (empKernel x) r γ π s - value P r γ π s)‖ ≤
        4 * γ * Real.sqrt (2 * Real.log
          (4 * Fintype.card S * Real.log (Real.exp 1 / (1 - γ)) / δ) / N) *
          ‖Matrix.mulVec (resolvent P γ π)
            (fun s => Real.sqrt (varPi P π (fun s' => value P r γ π s') s))‖ +
        (2 * γ * Real.log
          (4 * Fintype.card S * Real.log (Real.exp 1 / (1 - γ)) / δ) /
          ((1 - γ) * N)) * ‖(fun s => value P r γ π s)‖ ∧
       4 * γ * Real.sqrt (2 * Real.log
          (4 * Fintype.card S * Real.log (Real.exp 1 / (1 - γ)) / δ) / N) *
          ‖Matrix.mulVec (resolvent P γ π)
            (fun s => Real.sqrt (varPi P π (fun s' => value P r γ π s') s))‖ +
        (2 * γ * Real.log
          (4 * Fintype.card S * Real.log (Real.exp 1 / (1 - γ)) / δ) /
          ((1 - γ) * N)) * ‖(fun s => value P r γ π s)‖ ≤
        6 * Real.sqrt (2 * Real.log
          (4 * Fintype.card S * Real.log (Real.exp 1 / (1 - γ)) / δ) /
          (N * (1 - γ) ^ 3)))) ≤ δ := by sorry

end BreakingSample.Perturbed
