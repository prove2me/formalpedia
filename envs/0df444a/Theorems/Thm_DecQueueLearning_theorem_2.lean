-- Prove2me | Theorems.Thm_DecQueueLearning_theorem_2
-- name    : DecQueueLearning.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:42:33.94856+00:00
-- url     : https://prove2.me/theorems/b125a60b-d6fe-490e-af22-b30d28217b9e
-- title:
--   Theorem 2 — under DAM.FE, $\mathbb E[\frac1T\sum_t\sum_i\lambda_iQ_i(t)]=O(\frac{K^2}{\varepsilon^3}(\log N+K)L_{\mathrm{check}}+\frac{K\min(T,T_0)^2}{\varepsilon T})$
-- statement:
--   There is an absolute constant $C$ with the following property. Let $N\ge1$ queues and $K\ge1$ servers form a system with arrival rates $\lambda_i\in[0,1]$ and service rates $\mu_{i,j}\in\{0\}\cup[\delta,1]$, $\delta\in(0,1)$, with traffic slackness $\varepsilon\in(0,1]$, and let all queues follow DAM.FE with exploration parameter $\gamma\in(0,1)$ and arbitrary tie rules. Then for every horizon $T\ge1$,
--   $$
--   \mathbb E\Big[\frac1T\sum_{t=1}^T\sum_{i=1}^N\lambda_iQ_i(t)\Big]\ \le\ C\Big(\frac{K^2}{\varepsilon^3}(\log_2N+K)L_{\mathrm{check}}+\frac{K\min(T,T_0)^2}{\varepsilon T}\Big),
--   $$
--   with $L_{\mathrm{check}}$ from eq. (2) and $T_0=\ell_0L_{\mathrm{epoch}}+1$ from eq. (5).
--
--   The queues never learn the service rates in advance, communicate only through bids and binary feedback, and may face zero service rates; the bound is the known-rates guarantee plus a transient that vanishes as $T\to\infty$.
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
--   - reading: = O(·) for any T > 0 → ∃ C before all of N, K, the system, ε, δ, γ, the tie rules and T; reason: E.5 proves the bound with explicit absolute constants; a C depending on the instance would be a weaker stability statement
--   - encoding: any T > 0 → integer T ≥ 1; reason: the horizon counts time slots
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, Theorem 2, eq. (6), p.18 (PDF 19)

import Mathlib
import Definitions.Def_DecQueueLearning_System
import Definitions.Def_DecQueueLearning_Constants
import Definitions.Def_DecQueueLearning_TieRules
import Definitions.Def_DecQueueLearning_Auction
import Definitions.Def_DecQueueLearning_ProbSpace
import Definitions.Def_DecQueueLearning_Process

open MeasureTheory ProbabilityTheory Finset

namespace DecQueueLearning

/-- **Theorem 2**, Freund–Lykouris–Weng, arXiv:2206.03324v3, p. 18: "If all queues follow DAM.FE,
then for any T > 0 it holds that:
E[(1/T) Σ_{t=1}^T Σ_{i=1}^N λᵢ Qᵢ(t)] = O((K²/ε³)(log N + K) L_check + K min(T, T₀)²/(εT))."

The `O(·)` is an absolute constant `C`, chosen before everything else: one `C` for every number of
queues `N ≥ 1` and servers `K ≥ 1`, every system with arrival rates `λᵢ ∈ [0, 1]` and service
rates `µᵢⱼ ∈ {0} ∪ [δ, 1]` with traffic slackness `ε ∈ (0, 1]`, every `δ ∈ (0, 1)`, every
exploration parameter `γ ∈ (0, 1)`, all tie-breaking rules, and every horizon `T ≥ 1`.

**Formalization Note** `log` is `log₂` (as in eq. (2)). The conclusion also asserts that the
time-averaged weighted queue length is integrable. -/
theorem theorem_2 : ∃ C : ℝ, ∀ (N K : ℕ) [NeZero N] [NeZero K] (s : System N K) (ε δ γ : ℝ),
    0 < ε → ε ≤ 1 → 0 < δ → δ < 1 → 0 < γ → γ < 1 →
    HasTrafficSlackness s ε → HasRateLowerBound s δ → ∀ (rules : TieRules N K) (T : ℕ), 1 ≤ T →
    let P := damFEMeasure s γ
    let obj : Omega N K → ℝ := fun ω => (1 / (T : ℝ)) *
      ∑ t ∈ Icc 1 T, ∑ i, s.lam i * (queue ε δ rules (damFEPolicy ε δ) ω i t : ℝ)
    Integrable obj P ∧
      ∫ ω, obj ω ∂P ≤ C * ((K : ℝ) ^ 2 / ε ^ 3 * (Real.logb 2 N + K) * (Lcheck N K ε δ : ℝ) +
        K * (min (T : ℝ) (T0 N K ε δ γ : ℝ)) ^ 2 / (ε * T)) := by sorry

end DecQueueLearning
