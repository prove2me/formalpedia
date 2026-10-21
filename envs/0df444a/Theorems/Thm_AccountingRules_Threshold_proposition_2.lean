-- Prove2me | Theorems.Thm_AccountingRules_Threshold_proposition_2
-- name    : AccountingRules.Threshold.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:55.697007+00:00
-- url     : https://prove2.me/theorems/a673b088-2701-4f47-ae4a-2f68b13a5650
-- title:
--   Proposition 2 — corrected optimal accounting threshold and first-best case
-- statement:
--   Let the common prior $P$ have a density and full support $[\underline\theta,\overline\theta]$, with $0\le\underline\theta<M<\overline\theta$, and let the private continuation benefit satisfy $0<B\le M$ and $\underline\theta<M-B$. Then an optimal accounting rule among **all** Bayes-plausible distributions over posteriors reveals whether $\theta>\hat\theta$ for a threshold $\hat\theta\in(M-B,M]$:
--   $$h^*(\theta)=1\{\theta>\hat\theta\}.$$
--   If $B\le\mathbb E_P[M-\theta\mid\theta\le M]$, then $\hat\theta=M$. Otherwise $\hat\theta\in(M-B,M)$ is the unique solution of $\mathbb E_P[\theta\mid\theta\le\hat\theta]=M-B$. For the two signals of this rule, the entrepreneur continues after signal $1$ and terminates after signal $0$: $a^*(x)=x$.
--
--   The theorem characterizes when the first-best liquidation decision is possible and the threshold used when private benefits force additional disclosure.
--
--   **Formalization Note** This is a corrected endpoint version of Proposition 2. The paper allows $B=0$, when its claimed interval $(M-B,M]$ is empty, and $\underline\theta=M-B$, when the claimed interior root may fail. Assumption (1) is omitted because the paper's problem (5) and Appendix A.1 do not use it. Indifference leads to termination, and the high signal is the strict event $\theta>\hat\theta$. Conditional means are evaluated only on positive-probability events.
-- source:
--   Jiang & Yang, Optimal Accounting Rules, Private Benefits of Control, and Efficient Liquidation, Management Science (Articles in Advance, 2023), doi:10.1287/mnsc.2019.03087, pp. 4–5 (PDF 5–6), Proposition 2 and (6); p. 12 (PDF 13), endnote 6; corrected endpoint hypotheses

import Mathlib
import Definitions.Def_AccountingRules_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace AccountingRules.Threshold

/-- Proposition 2, pp. 4–5, with the necessary strict corner hypotheses. -/
theorem proposition_2 (P : Measure ℝ) (θlo θhi M B : ℝ)
    (hS : Standing P θlo θhi M B) (hlo : θlo < M - B) (hB : 0 < B) :
    ∃ θhat ∈ Ioc (M - B) M,
      (∀ τ : Measure (Measure ℝ), FinDisclosure.Threshold.IsBayesPlausible P τ →
          value M B τ ≤ value M B (FinDisclosure.Threshold.revealPolicy P (Ioi θhat))) ∧
      (B ≤ condMean P (fun θ => M - θ) (Iic M) → θhat = M) ∧
      (condMean P (fun θ => M - θ) (Iic M) < B →
          θhat ∈ Ioo (M - B) M ∧ condMean P id (Iic θhat) = M - B ∧
          ∀ t ∈ Ioo (M - B) M, condMean P id (Iic t) = M - B → t = θhat) ∧
      (M - B < postMean (P[|Ioi θhat]) ∧
        postMean (P[|Iic θhat]) ≤ M - B) := by sorry

end AccountingRules.Threshold
