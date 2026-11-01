-- Prove2me | Theorems.Thm_DecQueueLearning_lemma_3_1
-- name    : DecQueueLearning.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:42:39.306005+00:00
-- url     : https://prove2.me/theorems/19276262-878e-4cc8-846a-00ce1d54885b
-- title:
--   Lemma 3.1 — the good checking event has probability at least $1-\varepsilon/32$
-- statement:
--   Consider the DAM.K process: a system with traffic slackness $\varepsilon\in(0,1]$ and nonzero service rates at least $\delta\in(0,1)$, every queue running DAM.CONVERGE and DAM.COMMIT with weights $\mu_{i,j}Q_i(t_0)$ in every epoch, and arbitrary tie rules. For every epoch $\ell\ge1$, the good checking event $\mathcal E_\ell$ is an event and
--   $$
--   \mathbb P(\mathcal E_\ell)\ \ge\ 1-\tfrac1{32}\varepsilon .
--   $$
--   The bound is used to control the drift of an epoch in which the queues fail to detect that they are unmatched.
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
--   - encoding: ℰ_ℓ requires S_{I(j,t′),j}(t′) = 1 → a slot with I(j, t′) = ⊥ counts as a success; reason: the paper sets µ_{⊥,j} = 1 (p. 6)
--   - encoding: expectations and conditional expectations of the queue process → Bochner integrals / condExp, with conjuncts asserting the integrands integrable and Q(t₀) measurable; reason: a non-integrable integrand has integral 0 in Lean; the conjuncts rule that out; the paper's quantities are bounded random variables
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, Lemma 3.1, p.12 (PDF 13)

import Mathlib
import Definitions.Def_DecQueueLearning_System
import Definitions.Def_DecQueueLearning_Constants
import Definitions.Def_DecQueueLearning_TieRules
import Definitions.Def_DecQueueLearning_Auction
import Definitions.Def_DecQueueLearning_ProbSpace
import Definitions.Def_DecQueueLearning_Process

open MeasureTheory ProbabilityTheory Finset

namespace DecQueueLearning

/-- **Lemma 3.1**, Freund–Lykouris–Weng, arXiv:2206.03324v3, p. 12: "For epoch ℓ ≥ 1, the good
checking event ℰ_ℓ holds with probability at least 1 − (1/32)ε."

In the DAM.K process (Algorithm 1): every queue follows DAM.CONVERGE and DAM.COMMIT with weights
`µᵢⱼ Qᵢ(t₀)`, the primitives are independent with the laws of `damKMeasure`, and the tie rules
are arbitrary. The conclusion also asserts that `ℰ_ℓ` is an event (measurable). -/
theorem lemma_3_1 {N K : ℕ} [NeZero N] [NeZero K] (s : System N K) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1) (hslack : HasTrafficSlackness s ε)
    (hlow : HasRateLowerBound s δ) (rules : TieRules N K) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    let E := {ω : Omega N K | GoodChecking ε δ rules
      (epochAuction ε δ rules (damKPolicy s) ω ℓ) (services ω) (epochStart (Lepoch N K ε δ) ℓ)}
    MeasurableSet E ∧ ENNReal.ofReal (1 - ε / 32) ≤ damKMeasure s E := by sorry

end DecQueueLearning
