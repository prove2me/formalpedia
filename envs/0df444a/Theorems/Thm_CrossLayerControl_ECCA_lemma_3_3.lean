-- Prove2me | Theorems.Thm_CrossLayerControl_ECCA_lemma_3_3
-- name    : CrossLayerControl.ECCA.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:39:33.1559+00:00
-- url     : https://prove2.me/theorems/b6faf352-e3ed-4c0a-a1ae-3574422f1e58
-- title:
--   Lemma 3.3 (Necessary Condition for Strong Stability)
-- statement:
--   Let $(\Omega,\Pr)$ be a probability space, $U(0)\ge0$ integrable, $\mu(t)\ge0$ a measurable service process and $A(t)\ge0$ an integrable arrival process, and let $U(t+1)=\max[U(t)-\mu(t),0]+A(t)$. If the queue is strongly stable,
--   $$\limsup_{t\to\infty}\frac1t\sum_{\tau=0}^{t-1}\mathbb E\{U(\tau)\}<\infty,$$
--   and either $\mathbb E\{A(t)\}\le A_{max}$ for all $t$, or $\mu(t)$ is integrable and $\mathbb E\{\mu(t)-A(t)\}\le D_{max}$ for all $t$, for finite constants $A_{max},D_{max}\ge0$, then
--   $$\lim_{t\to\infty}\frac{\mathbb E\{U(t)\}}{t}=0.\tag{3.1}$$
--
--   Strong stability implies mean-rate stability; this is why the class of admissible policies of the mission, defined by mean-rate stability, contains the paper's strongly stable policies.
--
--   Differences from the source:
--   - reading: a queue with arbitrary arrival and server processes → U(0) ≥ 0 integrable, µ(t) ≥ 0 measurable, A(t) ≥ 0 integrable, and µ(t) integrable inside the second alternative; reason: backlogs, rates and arrivals are nonnegative in the model of §3.1; strong stability forces E U(0) < ∞ and E A(t) ≤ E U(t+1) < ∞, and E{µ(t) − A(t)} ≤ Dmax with A(t) integrable forces µ(t) integrable
--   - encoding: the constant Dmax; limsup < ∞ → the constant Dbd; limsup in EReal < ⊤; reason: Dmax is a different constant in Theorem 6.3; EReal makes the limsup honest
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, Lemma 3.3, p. 24

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_queueLaw
import Definitions.Def_CrossLayerControl_ECCA_IsStronglyStable

open MeasureTheory Filter Topology

namespace CrossLayerControl.ECCA

/-- **Lemma 3.3 (Necessary Condition for Strong Stability).**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), Lemma 3.3, p. 24: "If a queue is strongly stable and either
E{A(t)} ≤ Amax for all t, or E{µ(t)−A(t)} ≤ Dmax for all t, where Amax, Dmax are finite nonnegative
constants, then: lim_{t→∞} E{U(t)}/t = 0. (3.1)" The queue is that of §3.1, p. 23:
U(t + 1) = max[U(t) − µ(t), 0] + A(t), for "any arbitrary arrival and server processes" (p. 24).

Let `(Ω, Pr)` be a probability space, `U(0) = u₀ ≥ 0` integrable, `μ(t) ≥ 0` a (measurable)
service process and `A(t) ≥ 0` an integrable arrival process; let `U(t)` follow the queue law of
§3.1 on every sample path. If the queue is strongly stable (Definition 3.1) and either
`E A(t) ≤ Amax` for all `t`, or `μ(t)` is integrable and `E[μ(t) − A(t)] ≤ Dmax` for all `t`, for
finite constants `Amax, Dmax ≥ 0`, then `E U(t) / t → 0` as `t → ∞`.

**Formalization Note.** The bound `Dmax` of the lemma is named `Dbd` (it is unrelated to the
`Dmax` of Theorem 6.3). Nonnegativity of backlog, service and arrivals is that of the queueing model
of §3.1. Integrability of `U(0)` and of every `A(t)` is implied by strong stability, since
`U(t + 1) ≥ A(t)` and an infinite `E U(τ)` makes every later time average infinite. The service
process is only assumed measurable (it is a random process); its integrability is assumed only in
the second alternative, where `E{µ(t) − A(t)} ≤ Dmax` with `A(t)` integrable already forces it. -/
theorem lemma_3_3 {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (u₀ : Ω → ℝ) (μ A : ℕ → Ω → ℝ)
    (hu₀ : ∀ ω, 0 ≤ u₀ ω) (hu₀i : Integrable u₀ Pr)
    (hμ : ∀ t ω, 0 ≤ μ t ω) (hA : ∀ t ω, 0 ≤ A t ω)
    (hμm : ∀ t, AEStronglyMeasurable (μ t) Pr) (hAi : ∀ t, Integrable (A t) Pr)
    (hstab : IsStronglyStable Pr (fun t ω => queueLaw (u₀ ω) (fun τ => μ τ ω) (fun τ => A τ ω) t))
    (hbd : (∃ Amax : ℝ, 0 ≤ Amax ∧ ∀ t, ∫ ω, A t ω ∂Pr ≤ Amax) ∨
      (∃ Dbd : ℝ, 0 ≤ Dbd ∧ ∀ t, Integrable (μ t) Pr ∧ ∫ ω, (μ t ω - A t ω) ∂Pr ≤ Dbd)) :
    Tendsto (fun t : ℕ =>
        (∫ ω, queueLaw (u₀ ω) (fun τ => μ τ ω) (fun τ => A τ ω) t ∂Pr) / (t : ℝ))
      atTop (𝓝 0) := by sorry

end CrossLayerControl.ECCA
