-- Prove2me | Theorems.Thm_AvgCompletionSched_BestAlpha_random_alpha_bound
-- name    : AvgCompletionSched.BestAlpha.random_alpha_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:49:20.294145+00:00
-- url     : https://prove2.me/theorems/84ca325b-1379-491e-b2d5-2c7a0127ca35
-- title:
--   Lemma 2.5 — Random-$\alpha$: $E[C^\alpha_i]\le(1+\delta)C^P_i$
-- statement:
--   Let $P$ be any preemptive one-machine schedule of an instance with processing times $p_j>0$ and release dates $r_j\ge0$. Let $f$ be a probability density on $(0,1]$: $f\ge0$ on $(0,1]$, $f$ integrable on $[0,1]$, and $\int_0^1 f=1$. Let $\delta$ be any real number with
--   $$\int_0^\beta\frac{1+\alpha-\beta}{\beta}f(\alpha)\,d\alpha\le\delta\qquad\text{for all }\beta\in(0,1].$$
--   Draw $\alpha$ with density $f$ and let $C^\alpha_i$ be the completion time of $J_i$ in the $\alpha$-schedule (ties broken by job index). Then for every job $J_i$ the map $\alpha\mapsto f(\alpha)C^\alpha_i$ is integrable on $[0,1]$ and
--   $$E[C^\alpha_i]=\int_0^1 f(\alpha)\,C^\alpha_i\,d\alpha\le(1+\delta)\,C^P_i,$$
--   and consequently $E\bigl[\sum_i C^\alpha_i\bigr]\le(1+\delta)\sum_i C^P_i$.
--
--   Choosing different densities in this bound gives the three parts of Theorem 2.6.
--
--   **Formalization Note** The paper's $\delta=\max_{0<\beta\le1}\int_0^\beta\frac{1+\alpha-\beta}{\beta}f(\alpha)\,d\alpha$ is replaced by an arbitrary upper bound $\delta$ of these integrals; the statement for every such $\delta$ is equivalent to the paper's statement with $\delta$ the supremum, and it avoids assuming that the maximum is attained. Integrability of the expectation is part of the conclusion.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 153, Lemma 2.5 (proof pp. 153–154)

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

namespace AvgCompletionSched.BestAlpha
theorem random_alpha_bound {n : ℕ} {I : Instance n} (P : PreemptiveSchedule I)
    (f : ℝ → ℝ) (hf_nonneg : ∀ α ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ f α)
    (hf_int : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hf_one : ∫ α in (0 : ℝ)..1, f α = 1)
    (δ : ℝ) (hδ : ∀ β ∈ Set.Ioc (0 : ℝ) 1, ∫ α in (0 : ℝ)..β, (1 + α - β) / β * f α ≤ δ) :
    (∀ i, IntervalIntegrable (fun α => f α * P.Calpha α i) MeasureTheory.volume 0 1 ∧
        ∫ α in (0 : ℝ)..1, f α * P.Calpha α i ≤ (1 + δ) * P.CP i) ∧
      ∫ α in (0 : ℝ)..1, f α * ∑ i, P.Calpha α i ≤ (1 + δ) * ∑ i, P.CP i := by sorry
end AvgCompletionSched.BestAlpha
