-- Prove2me | Theorems.Thm_DecQueueLearning_lemma_4_4
-- name    : DecQueueLearning.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:42:23.04537+00:00
-- url     : https://prove2.me/theorems/fa2e32a7-528c-4e16-b47e-594cd472389b
-- title:
--   Lemma 4.4 — drift when all queues exploit with accurate estimates
-- statement:
--   In the DAM.FE process, for every epoch $\ell\ge1$ whose start $t_0$ satisfies $t_0\ge T_0$, with $D=V(Q(t_0+L_{\mathrm{epoch}}))-V(Q(t_0))$:
--   $$
--   \mathbb E[D\mid\mathcal E_P^c\cap\mathcal E_W^c]\,\mathbb P\{\mathcal E_P^c\cap\mathcal E_W^c\}\ \le\ 5781\frac{K}{\varepsilon^2}L_{\mathrm{conv}}^2-\frac32L_{\mathrm{conv}}\sum_{i=1}^N\lambda_i\mathbb E[Q_i(t_0)].
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
--   - encoding: E[X | A] P{A} → E[X·1_A]; reason: equal when P{A} > 0, and no division by a possibly zero P{A}
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, Lemma 4.4, p.19 (PDF 20)

import Mathlib
import Definitions.Def_DecQueueLearning_System
import Definitions.Def_DecQueueLearning_Constants
import Definitions.Def_DecQueueLearning_TieRules
import Definitions.Def_DecQueueLearning_Auction
import Definitions.Def_DecQueueLearning_ProbSpace
import Definitions.Def_DecQueueLearning_Process

open MeasureTheory ProbabilityTheory Finset

namespace DecQueueLearning

/-- **Lemma 4.4**, Freund–Lykouris–Weng, arXiv:2206.03324v3, p. 19: "If t₀ ≥ T₀, it holds that:
E[V(Q(t₀ + L_epoch)) − V(Q(t₀)) | ℰ_P^c ∩ ℰ_W^c] P{ℰ_P^c ∩ ℰ_W^c}
≤ 5781 (K/ε²) L_conv² − (3/2) L_conv Σᵢ λᵢ E[Qᵢ(t₀)]."

In the DAM.FE process, for every epoch `ℓ ≥ 1` whose start `t₀` satisfies `t₀ ≥ T₀`.

**Formalization Note** `E[X | A] P{A}` is written `E[X 1_A]`. The conclusion also asserts that
every integrand is integrable. -/
theorem lemma_4_4 {N K : ℕ} [NeZero N] [NeZero K] (s : System N K) (ε δ γ : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hslack : HasTrafficSlackness s ε) (hlow : HasRateLowerBound s δ) (rules : TieRules N K) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hT0 : T0 N K ε δ γ ≤ epochStart (Lepoch N K ε δ) ℓ) :
    let P := damFEMeasure s γ
    let t0 := epochStart (Lepoch N K ε δ) ℓ
    let L := Lepoch N K ε δ
    let Lc := Lconv N K ε δ
    let Q : Omega N K → ℕ → Fin N → ℕ := fun ω t i => queue ε δ rules (damFEPolicy ε δ) ω i t
    let D : Omega N K → ℝ := fun ω => lyapunov (Q ω (t0 + L)) - lyapunov (Q ω t0)
    let EP := {ω : Omega N K | EventP ω ℓ}
    let EW := {ω : Omega N K | EventW s ε δ rules ω ℓ}
    (∀ i, Integrable (fun ω => (Q ω t0 i : ℝ)) P) ∧
    Integrable ((EPᶜ ∩ EWᶜ).indicator D) P ∧
      ∫ ω, (EPᶜ ∩ EWᶜ).indicator D ω ∂P ≤
        5781 * (K / ε ^ 2) * (Lc : ℝ) ^ 2 - 3 / 2 * (Lc : ℝ) * ∑ i, s.lam i * ∫ ω, (Q ω t0 i : ℝ) ∂P := by sorry

end DecQueueLearning
