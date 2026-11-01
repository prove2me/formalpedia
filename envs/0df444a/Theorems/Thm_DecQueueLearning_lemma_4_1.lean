-- Prove2me | Theorems.Thm_DecQueueLearning_lemma_4_1
-- name    : DecQueueLearning.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:42:32.111422+00:00
-- url     : https://prove2.me/theorems/aa72b0f7-5fa1-4fe8-aaa4-bca1bdf6d9f1
-- title:
--   Lemma 4.1 (corrected: guarded by the explorer outbidding the exploiting queues) — the samples collected by DAM.UPDATE are i.i.d. Bernoulli($\mu_{i,j}$)
-- statement:
--   In the DAM.FE process (traffic slackness $\varepsilon\in(0,1]$, rates in $\{0\}\cup[\delta,1]$ with $\delta\in(0,1)$, exploration parameter $\gamma\in(0,1)$, arbitrary tie rules), let $\mathcal Y_{i,j}(t_0)$ be the samples between queue $i$ and server $j$ collected by DAM.UPDATE up to the start $t_0$ of an epoch. All of them are almost surely independent and Bernoulli with mean $\mu_{i,j}$: for every pair $(i,j)$ there is a sequence $X_0,X_1,\dots$ of independent $\mathrm{Bernoulli}(\mu_{i,j})$ random variables such that, almost surely, for every epoch $\ell\ge1$ such that queue $i$ outbid every non-exploring queue at $j$ in each earlier epoch in which it explored $j$, the samples collected up to its start are, in the order collected, $X_0,X_1,\dots,X_{n_{i,j}(t_0)-1}$.
--
--   It is what makes the empirical means concentrate even though the number of samples is random.
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
--   - reading: all random variables in 𝒴ᵢⱼ(t₀) are a.s. independent and Bernoulli(µᵢⱼ) → the collected samples, in order, are a.s. a prefix of one i.i.d. Bernoulli(µᵢⱼ) sequence fixed in advance, simultaneously for all epochs; reason: the number of samples is random; this is the standard meaning (optional skipping) and the one the concentration step in E.2 uses
--   - correction: all samples are independent Bernoulli(µᵢⱼ) with no condition; the proof (p. 50) says an explorer outbids every non-exploring queue, bid at most t₀ → the prefix claim is guarded by ExplorerOutbids for (i, j) in every epoch before ℓ; reason: the printed lemma is false: an exploiter's bid can reach Qᵢ(t₀)(1 + ε/16) (Algorithm 2, lines 7–8). N = 2, K = 1, ε = 1, δ = γ = 1/2, λ ≡ 1/16, µ ≡ 1/2, η₂ < η₁: with positive probability queue 1 gets n₁₁ = 1, µ̂₁₁ = 1 in epoch 1, is then never served and receives a job in every slot, and queue 2 explores in a late epoch and is served at t₀; queue 1's bid (17/16)(1 − η₁)Q₁(t₀) passes queue 2's bid within the converge phase and queue 2's remaining samples are forced to 0, so the sample stream has mean below µ₂₁. Such epochs are a.s. finitely many (λᵢ ≤ 1/(1 + ε))
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, Lemma 4.1, pp.17–18 (PDF 18–19)

import Mathlib
import Definitions.Def_DecQueueLearning_System
import Definitions.Def_DecQueueLearning_Constants
import Definitions.Def_DecQueueLearning_TieRules
import Definitions.Def_DecQueueLearning_Auction
import Definitions.Def_DecQueueLearning_ProbSpace
import Definitions.Def_DecQueueLearning_Process

open MeasureTheory ProbabilityTheory Finset

namespace DecQueueLearning

/-- **Lemma 4.1**, Freund–Lykouris–Weng, arXiv:2206.03324v3, pp. 17–18: "Let t₀ be the start of an
epoch and let 𝒴ᵢⱼ(t₀) by the set of samples between queue i ∈ 𝒩 and server j ∈ 𝒦 collected by
Algorithm 5 up to time slot t₀. Then all random variables in 𝒴ᵢⱼ(t₀) are almost surely independent
and Bernoulli distributed with mean µᵢⱼ."

In the DAM.FE process (Algorithm 4).

**Formalization Note** The number of collected samples is random, so the statement is read as: for
every pair `(i, j)` there is an i.i.d. sequence `X₀, X₁, …` of Bernoulli(`µᵢⱼ`) random variables
such that, almost surely, for every epoch `ℓ ≥ 1` the samples collected up to its start, in the
order collected, are `X₀, X₁, …, X_{nᵢⱼ(t₀) − 1}`.

**Correction** The printed lemma is false, and the guard `ExplorerOutbids` for the epochs before
`ℓ` is added. Its proof (p. 50) uses that an explorer outbids every exploiting queue, but an
exploiter's bid can reach `Qᵢ(t₀)(1 + ε/16)`. Take `N = 2`, `K = 1`, `ε = 1`, `δ = γ = 1/2`,
`λ ≡ 1/16`, `µ ≡ 1/2`. With positive probability queue 1 gets `n₁₁ = 1`, `µ̂₁₁ = 1` in epoch 1, is
then never served and receives a job in every slot, so `µ̄₁₁ = 1` and `Q₁(t₀) ≥ t₀ − 3`, while
queue 2 (`η₂ < η₁`, so it has no sample from epoch 1) explores in a later epoch and is served at
`t₀`. Queue 1's bid passes
`(t₀ + L_epoch + 1)(1 + η₂)` within the converge phase, once `(1 + 1/16)(1 − η₁)(t₀ − 3)` exceeds
that bid, and queue 2's remaining samples in the epoch are forced to `0`. So the collected sample
is `1` with conditional probability `0`, not `1/2`, on an event of positive probability. -/
theorem lemma_4_1 {N K : ℕ} [NeZero N] [NeZero K] (s : System N K) (ε δ γ : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hslack : HasTrafficSlackness s ε) (hlow : HasRateLowerBound s δ) (rules : TieRules N K) :
    let P := damFEMeasure s γ
    ∀ i j, ∃ X : ℕ → Omega N K → Bool, (∀ k, Measurable (X k)) ∧ iIndepFun X P ∧
      (∀ k, P.map (X k) = bern (s.mu i j)) ∧
      ∀ᵐ ω ∂P, ∀ ℓ, 1 ≤ ℓ → (∀ m, 1 ≤ m → m < ℓ → ExplorerOutbids ε δ rules ω i j m) →
        ∀ k (hk : k < (collectedSamples ε δ rules ω i j ℓ).length),
          (collectedSamples ε δ rules ω i j ℓ)[k] = X k ω := by sorry

end DecQueueLearning
