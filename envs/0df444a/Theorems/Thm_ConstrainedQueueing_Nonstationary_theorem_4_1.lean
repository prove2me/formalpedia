-- Prove2me | Theorems.Thm_ConstrainedQueueing_Nonstationary_theorem_4_1
-- name    : ConstrainedQueueing.Nonstationary.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:01.997867+00:00
-- url     : https://prove2.me/theorems/6d298117-b623-4879-9e9b-5710893e1860
-- title:
--   Theorem 4.1, p. 1941 — for a ∉ C̄′, Σ_l X_l(t) → ∞ a.s. under every history-dependent policy
-- statement:
--   Consider a constrained queueing network with a single class of customers and one-slot service times: $L$ queues, $N$ servers, server $i$ moving one customer per activated slot from queue $q(i)$ to queue $h(i)$ or out of the system, and a constraint set $S$ of activation sets that satisfies C.1 and contains the empty set. The arrivals $A_l(t)$ at queue $l$ in slot $t$ are i.i.d. over $t$, independent across queues, with finite second moments; let $a_l=E[A_l(1)]$ be the arrival rates.
--
--   **Theorem 4.1.** If $a\notin\bar C'$, then for every policy $\pi\in\tilde G$ (every rule choosing, in each slot, an activation set as a function of the whole history of queue lengths, and never activating more servers of a queue than it has customers) and every initial state, the total number of customers in the system grows to infinity:
--   $$\lim_{t\to\infty}\sum_{l=1}^L X_l(t)=\infty\quad\text{a.s.} \tag{4.1}$$
--
--   Together with the fact that a stationary policy stabilizes the system for every $a\in C'$ (Theorem 3.2 of the paper), this shows that nonstationary, history-dependent policies gain nothing in stability: the region $\bar C'$, determined by flows bounded by the convex hull of the activation vectors, is the limit of what any scheduler can sustain.
--
--   **Formalization Note.** The page states the theorem for $a\in\bar C^c$, the complement of the closure of the stability region $C$ of Definition 3.4; the introduction of §IV states it for $(\bar C')^c$, and $\bar C=\bar C'$ by Theorem 3.2. The formalization uses $\bar C'$, defined from flows (`Cprime`). Queues and servers are indexed from 0. `A t` is the arrival vector of slot $t+1$; the standing assumptions of §II become: `iIndepFun` of the vectors over time, `IdentDistrib` with `A 0`, `iIndepFun` of the components within each slot, and integrability of $A_l^2$. The rate $a$ is the mean of `A 0`. A policy maps the history $X(0),\dots,X(t)$ to the activation set of slot $t+1$ and is admissible (`IsAdmissiblePolicy`: sets in $S$, no server activated for a nonexisting customer, the defining property of activation rules on p. 1938). `X t ω` is the run of (2.1) with $M\equiv I$ for the arrivals of outcome $\omega$. The hypothesis $\emptyset\in S$ is the paper's standing convention.
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), p. 1941, §IV, Theorem 4.1, (4.1); statistical assumptions p. 1938

import Mathlib
import Definitions.Def_ConstrainedQueueing_Nonstationary_Model

namespace ConstrainedQueueing.Nonstationary

open MeasureTheory ProbabilityTheory Filter

/-- Theorem 4.1 (p. 1941): single class, one-slot service times. Let the arrival vectors `A t`
(arrivals at the `L` queues in slot `t + 1`) be i.i.d. in time, with independent components and
finite second moments, and let `a` be their mean. If `a` lies outside the closure of `C'`, then
for every admissible history-dependent policy `π` and every initial state, the total number of
customers in the system tends to infinity almost surely. -/
theorem theorem_4_1 {L N : ℕ} (net : Network L N) (hC1 : C1 net)
    (hS0 : (∅ : Finset (Fin N)) ∈ net.S)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Fin L → ℕ) (hAmeas : ∀ t, Measurable (A t))
    (hindep : iIndepFun (fun t => A t) μ) (hident : ∀ t, IdentDistrib (A t) (A 0) μ μ)
    (hindepQ : ∀ t, iIndepFun (fun l ω => A t ω l) μ)
    (hsq : ∀ l, Integrable (fun ω => ((A 0 ω l : ℝ)) ^ 2) μ)
    (a : Fin L → ℝ) (hmean : ∀ l, a l = ∫ ω, (A 0 ω l : ℝ) ∂μ)
    (ha : a ∉ closure (Cprime net))
    (π : HistPolicy L N) (hπ : IsAdmissiblePolicy net π) (x0 : Fin L → ℕ)
    (X : ℕ → Ω → Fin L → ℕ) (hX : ∀ ω, IsRun net π x0 (fun t => A t ω) (fun t => X t ω)) :
    ∀ᵐ ω ∂μ, Tendsto (fun t => ∑ l, (X t ω l : ℝ)) atTop atTop := by sorry

end ConstrainedQueueing.Nonstationary
