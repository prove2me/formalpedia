-- Prove2me | Theorems.Thm_ConstrainedQueueing_Nonstationary_display_4_12
-- name    : ConstrainedQueueing.Nonstationary.display_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:50.963461+00:00
-- url     : https://prove2.me/theorems/f29982a1-f940-41b5-a0c4-eebbfc2656f2
-- title:
--   (4.12), proof of Theorem 4.1, p. 1943 — Σ_{τ=1}^t (Σ_{l∈Q}(A_l(τ) − a_l) + ε) → ∞ a.s. for every Q
-- statement:
--   Let $A(1),A(2),\dots$ be independent, identically distributed random vectors in $\mathbb N^L$ on a probability space, with integrable components and means $a_l=E[A_l(1)]$, and let $\epsilon>0$. Then for every set $Q\subseteq\{1,\dots,L\}$ of queues,
--   $$\lim_{t\to\infty}\sum_{\tau=1}^{t}\Big(\sum_{l\in Q}\big(A_l(\tau)-a_l\big)+\epsilon\Big)=\infty\quad\text{a.s.} \tag{4.12}$$
--   since the summands are i.i.d. with expected value $\epsilon>0$.
--
--   Together with the pathwise bound (4.7), which holds for every policy, this gives Theorem 4.1: the total number of customers dominates the minimum of finitely many sequences, each of which tends to infinity almost surely.
--
--   **Formalization Note.** In Lean `A τ` is the arrival vector of slot $\tau+1$ and the sum is over `τ ∈ range t`; the page's lower limit $\tau=0$ is read as $\tau=1$ (see (4.10)). Independence is `iIndepFun` of the vectors over time and identical distribution is `IdentDistrib` with `A 0`. Only first moments are assumed, which is weaker than the paper's standing finite second moments; independence across queues within a slot is not needed and is not assumed. The quantifier $\forall Q$ is outside the almost-sure event, as on the page ($2^L$ sets, so the order does not matter).
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), p. 1943, proof of Theorem 4.1, (4.12)

import Mathlib

namespace ConstrainedQueueing.Nonstationary

open MeasureTheory ProbabilityTheory Filter

/-- Display (4.12), proof of Theorem 4.1 (p. 1943): if the arrival vectors `A τ` (arrivals at the
`L` queues in slot `τ + 1`) are independent and identically distributed with integrable
components of means `a_l`, then for every `ε > 0` and every set `Q` of queues the partial sums of
`∑_{l∈Q} (A_l(τ) - a_l) + ε` tend to `+∞` almost surely. -/
theorem display_4_12 {L : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ℕ → Ω → Fin L → ℕ) (hAmeas : ∀ t, Measurable (A t))
    (hindep : iIndepFun (fun t => A t) μ) (hident : ∀ t, IdentDistrib (A t) (A 0) μ μ)
    (hint : ∀ l, Integrable (fun ω => (A 0 ω l : ℝ)) μ)
    (a : Fin L → ℝ) (ha : ∀ l, a l = ∫ ω, (A 0 ω l : ℝ) ∂μ) (ε : ℝ) (hε : 0 < ε) :
    ∀ Q : Finset (Fin L), ∀ᵐ ω ∂μ,
      Tendsto (fun t => ∑ τ ∈ Finset.range t, (∑ l ∈ Q, ((A τ ω l : ℝ) - a l) + ε))
        atTop atTop := by sorry

end ConstrainedQueueing.Nonstationary
