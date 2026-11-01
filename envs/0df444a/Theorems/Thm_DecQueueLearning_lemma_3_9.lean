-- Prove2me | Theorems.Thm_DecQueueLearning_lemma_3_9
-- name    : DecQueueLearning.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:42:23.616438+00:00
-- url     : https://prove2.me/theorems/4a294b8e-8f20-4805-b5a5-39f0b6dbc1e0
-- title:
--   Lemma 3.9 — drift of the converge phase
-- statement:
--   In the DAM.K process (traffic slackness $\varepsilon\in(0,1]$, rates in $\{0\}\cup[\delta,1]$ with $\delta\in(0,1)$, arbitrary tie rules), for every epoch $\ell\ge1$ with start $t_0=(\ell-1)L_{\mathrm{epoch}}+1$, almost surely
--   $$
--   \mathbb E\big[V(Q(t_0+L_{\mathrm{conv}}))-V(Q(t_0))\,\big|\,Q(t_0)\big]\ \le\ 2L_{\mathrm{conv}}\sum_{i=1}^N\lambda_iQ_i(t_0)+KL_{\mathrm{conv}}^2 ,
--   $$
--   where $V(Q)=\sum_iQ_i^2$. It bounds the increase of the Lyapunov function while the queues are still converging.
--
--   Differences from the source:
--   - encoding: queues 𝒩 = [N], servers 𝒦 = [K], no request ⊥ → Fin N, Fin K (paper index = Lean index + 1), Option with none for ⊥; reason: Lean convention; same instances
--   - encoding: N queues and K servers → N ≥ 1 and K ≥ 1 ([NeZero N], [NeZero K]); reason: the system has queues and servers; log N and the uniform server sample are undefined otherwise
--   - reading: log in eq. (2) (base unstated) → log₂ (Real.logb 2) in ξ, L_conv and the stated bound; reason: the proof of Lemma 3.6 (D.5, p. 42) bounds ⌈68pK/ε⌉(L_check + 1) by 91 (log N) K L_check/ε with p < log N halvings, which needs base 2
--   - reading: a lower bound δ on the nonzero rates, µᵢⱼ ∈ {0} ∪ [δ, 1] → 0 < δ < 1; reason: eq. (2) uses ln(1 − δ), undefined at δ = 1
--   - reading: Algorithm 2, line 1: pᵢⱼ(t₀) ← 0, while line 6 at t = t₀ reads pᵢⱼ(t₀ − 1) → pᵢⱼ(t₀ − 1) = 0 and τᵢ(t₀ − 1) = t₀ − 1; reason: the prices read in the first slot of the epoch are the initial ones
--   - reading: Algorithm 2, line 13: 'Price updates for some server j' → only line 8 sets τᵢ(t) ← t; line 10 leaves τᵢ unchanged; reason: after line 10 every payoff is nonpositive and the prices are frozen, so the queue stays at ⊥ whichever way τᵢ moves; same process
--   - reading: Algorithm 3: for t = t_s to t_e − 1 → DAM.COMMIT requests in every slot of [t_s, t_e], inclusive of t_e; reason: Algorithms 1 and 4 call it on [t₀ + L_conv, t₀ + L_epoch − 1]; p. 20 ('keeps requesting … in [t₀ + L_conv, t₀ + L_epoch − 1]') and Lemma 4.1 need every slot
--   - reading: ties broken arbitrarily (footnote 2, p. 7; arg max in Algorithm 2, line 6) → every tie rule (TieRules), which may depend on the queue or server and on the slot, measurable in the bids; reason: measurability is what makes the queue lengths random variables
--   - reading: arrivals w.p. λᵢ, service w.p. µ_{I(j,t),j}, ηᵢ uniform on (0, 10⁻⁹), E_ℓ ~ Bernoulli(min(1, K/ℓ^γ)), σ(i) uniform → mutually independent primitives with these laws on a product space (damKMeasure / damFEMeasure), one service coin per pair and slot; reason: the model's independence is implicit; per-pair coins give each selected request success probability µ_{I(j,t),j}
--   - encoding: expectations and conditional expectations of the queue process → Bochner integrals / condExp, with conjuncts asserting the integrands integrable and Q(t₀) measurable; reason: a non-integrable integrand has integral 0 in Lean; the conjuncts rule that out; the paper's quantities are bounded random variables
--   - encoding: E[· | Q(t₀)] → condExp with respect to σ(Q(t₀)), the inequality holding almost surely; reason: standard meaning of conditioning on a random vector
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, Lemma 3.9, p.16 (PDF 17)

import Mathlib
import Definitions.Def_DecQueueLearning_System
import Definitions.Def_DecQueueLearning_Constants
import Definitions.Def_DecQueueLearning_TieRules
import Definitions.Def_DecQueueLearning_Auction
import Definitions.Def_DecQueueLearning_ProbSpace
import Definitions.Def_DecQueueLearning_Process

open MeasureTheory ProbabilityTheory Finset

namespace DecQueueLearning

/-- **Lemma 3.9**, Freund–Lykouris–Weng, arXiv:2206.03324v3, p. 16: "It holds that
E[V(Q(t₀ + L_conv)) − V(Q(t₀)) | Q(t₀)] ≤ 2 L_conv Σᵢ λᵢ Qᵢ(t₀) + K L_conv²."

In the DAM.K process, for every epoch `ℓ ≥ 1` with start `t₀ = (ℓ − 1) L_epoch + 1`, almost
surely. The conclusion also asserts that `Q(t₀)` is a random vector and the drift is integrable,
so that the conditional expectation is the genuine one. -/
theorem lemma_3_9 {N K : ℕ} [NeZero N] [NeZero K] (s : System N K) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1) (hslack : HasTrafficSlackness s ε)
    (hlow : HasRateLowerBound s δ) (rules : TieRules N K) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    let P := damKMeasure s
    let t0 := epochStart (Lepoch N K ε δ) ℓ
    let Lc := Lconv N K ε δ
    let Q : Omega N K → ℕ → Fin N → ℕ := fun ω t i => queue ε δ rules (damKPolicy s) ω i t
    Measurable (fun ω => Q ω t0) ∧
    Integrable (fun ω => lyapunov (Q ω (t0 + Lc)) - lyapunov (Q ω t0)) P ∧
    condExp (MeasurableSpace.comap (fun ω => Q ω t0) inferInstance) P
        (fun ω => lyapunov (Q ω (t0 + Lc)) - lyapunov (Q ω t0))
      ≤ᵐ[P] fun ω => 2 * (Lc : ℝ) * ∑ i, s.lam i * (Q ω t0 i : ℝ) + K * (Lc : ℝ) ^ 2 := by sorry

end DecQueueLearning
