-- Prove2me | Theorems.Thm_DecQueueLearning_lemma_4_2
-- name    : DecQueueLearning.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:42:13.859985+00:00
-- url     : https://prove2.me/theorems/cca43788-68e1-4667-b06d-f25693133441
-- title:
--   Lemma 4.2 — after $T_0$, exploration and wrong estimates are rare
-- statement:
--   In the DAM.FE process, for every epoch $\ell\ge1$ whose start $t_0=(\ell-1)L_{\mathrm{epoch}}+1$ satisfies $t_0\ge T_0$, the sets $\mathcal E_P$ (some queue explores in the epoch) and $\mathcal E_W$ (some pair with $\mu_{i,j}>0$ has an estimate outside its confidence bound, or a confidence radius above $\tfrac1{16}\varepsilon\delta$) are events and
--   $$
--   \mathbb P\{\mathcal E_P\}\le\frac1{L_{\mathrm{epoch}}}\qquad\text{and}\qquad\mathbb P\{\mathcal E_W\}\le\frac1{NKt_0^2}.
--   $$
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
--   - encoding: ∆ᵢⱼ(t₀) = √(3 ln t₀ / nᵢⱼ(t₀)), ∞ when nᵢⱼ(t₀) = 0 → the disjunct nᵢⱼ(t₀) = 0 in ℰ_W; reason: in Lean √(x/0) = 0; the disjunct makes an unsampled pair count as ∆ = ∞ > εδ/16
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, Lemma 4.2, p.19 (PDF 20)

import Mathlib
import Definitions.Def_DecQueueLearning_System
import Definitions.Def_DecQueueLearning_Constants
import Definitions.Def_DecQueueLearning_TieRules
import Definitions.Def_DecQueueLearning_Auction
import Definitions.Def_DecQueueLearning_ProbSpace
import Definitions.Def_DecQueueLearning_Process

open MeasureTheory ProbabilityTheory Finset

namespace DecQueueLearning

/-- **Lemma 4.2**, Freund–Lykouris–Weng, arXiv:2206.03324v3, p. 19: "If t₀ ≥ T₀, queues explore with
low probability and estimate accurate service rate estimations with high probability, i.e.,
P{ℰ_P} ≤ 1/L_epoch and P{ℰ_W} ≤ 1/(N K t₀²)."

In the DAM.FE process, for every epoch `ℓ ≥ 1` whose start `t₀ = (ℓ − 1) L_epoch + 1` satisfies
`t₀ ≥ T₀`; both bounds, and both sets are events. -/
theorem lemma_4_2 {N K : ℕ} [NeZero N] [NeZero K] (s : System N K) (ε δ γ : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hslack : HasTrafficSlackness s ε) (hlow : HasRateLowerBound s δ) (rules : TieRules N K) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hT0 : T0 N K ε δ γ ≤ epochStart (Lepoch N K ε δ) ℓ) :
    let P := damFEMeasure s γ
    let t0 := epochStart (Lepoch N K ε δ) ℓ
    MeasurableSet {ω : Omega N K | EventP ω ℓ} ∧
      P {ω | EventP ω ℓ} ≤ ENNReal.ofReal (1 / (Lepoch N K ε δ : ℝ)) ∧
    MeasurableSet {ω | EventW s ε δ rules ω ℓ} ∧
      P {ω | EventW s ε δ rules ω ℓ} ≤ ENNReal.ofReal (1 / ((N : ℝ) * K * (t0 : ℝ) ^ 2)) := by sorry

end DecQueueLearning
