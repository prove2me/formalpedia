-- Prove2me | Theorems.Thm_DecQueueLearning_lemma_3_6
-- name    : DecQueueLearning.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:40:58.687778+00:00
-- url     : https://prove2.me/theorems/47bf7cd8-d28d-4dbd-b505-3f45e6e28415
-- title:
--   Lemma 3.6 — convergence within $(99KL_{\mathrm{check}}/\varepsilon)(\log N+K)$ slots
-- statement:
--   Run the epoch auction with general nonnegative weights $w$ starting at slot $t_0$, assume the good checking event $\mathcal E_\ell$ holds on the path and that no two queues send equal bids to one server in the epoch. Then the system converges within
--   $$
--   \frac{99KL_{\mathrm{check}}}{\varepsilon}(\log_2N+K)
--   $$
--   slots: there is a slot $t\ge t_0$ with $t-t_0+1\le\frac{99KL_{\mathrm{check}}}{\varepsilon}(\log_2N+K)$ at which $|R_j(t)|\le1$ for every server $j$. In particular the system has converged before the end $t_0+L_{\mathrm{conv}}-1$ of the converge phase.
--
--   Differences from the source:
--   - encoding: queues 𝒩 = [N], servers 𝒦 = [K], no request ⊥ → Fin N, Fin K (paper index = Lean index + 1), Option with none for ⊥; reason: Lean convention; same instances
--   - reading: log in eq. (2) (base unstated) → log₂ (Real.logb 2) in ξ, L_conv and the stated bound; reason: the proof of Lemma 3.6 (D.5, p. 42) bounds ⌈68pK/ε⌉(L_check + 1) by 91 (log N) K L_check/ε with p < log N halvings, which needs base 2
--   - reading: a lower bound δ on the nonzero rates, µᵢⱼ ∈ {0} ∪ [δ, 1] → 0 < δ < 1; reason: eq. (2) uses ln(1 − δ), undefined at δ = 1
--   - reading: Algorithm 2, line 1: pᵢⱼ(t₀) ← 0, while line 6 at t = t₀ reads pᵢⱼ(t₀ − 1) → pᵢⱼ(t₀ − 1) = 0 and τᵢ(t₀ − 1) = t₀ − 1; reason: the prices read in the first slot of the epoch are the initial ones
--   - reading: Algorithm 2, line 13: 'Price updates for some server j' → only line 8 sets τᵢ(t) ← t; line 10 leaves τᵢ unchanged; reason: after line 10 every payoff is nonpositive and the prices are frozen, so the queue stays at ⊥ whichever way τᵢ moves; same process
--   - reading: ties broken arbitrarily (footnote 2, p. 7; arg max in Algorithm 2, line 6) → every tie rule (TieRules), which may depend on the queue or server and on the slot, measurable in the bids; reason: measurability is what makes the queue lengths random variables
--   - generalization: weights wᵢⱼ = µ̃ᵢⱼ Qᵢ(t₀) of an epoch of the process, started at t₀ = (ℓ − 1)L_epoch + 1 → any nonnegative weights w, any start t₀ ≥ 1, any perturbations ηᵢ ∈ (0, 10⁻⁹), any service-coin path S; reason: p. 13: the results of §3.3 'hold for general wᵢⱼ'; the epoch of DAM.K is the instance w = µQ(t₀) (proved by rfl in the sanity file)
--   - encoding: ℰ_ℓ requires S_{I(j,t′),j}(t′) = 1 → a slot with I(j, t′) = ⊥ counts as a success; reason: the paper sets µ_{⊥,j} = 1 (p. 6)
--   - reading: ties are broken arbitrarily and a.s. do not exist (footnote 2, p. 7) → hypothesis NoBidTies: no two queues send equal bids to one server in a slot of the epoch; reason: with an exact tie a slot-dependent tie rule can serve two tied queues alternately, so neither updates and the system never converges
--   - reading: converges in at most X time slots → some slot t with t − t₀ + 1 ≤ X (counting the slots t₀, …, t) has |R_j(t)| ≤ 1 for all j; reason: the reading the proof of Lemma 3.2 uses: convergence by t₀ + L_conv − 1
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, Lemma 3.6, p.14 (PDF 15)

import Mathlib
import Definitions.Def_DecQueueLearning_Constants
import Definitions.Def_DecQueueLearning_TieRules
import Definitions.Def_DecQueueLearning_Auction

namespace DecQueueLearning

/-- **Lemma 3.6** (convergence within an epoch), Freund–Lykouris–Weng, arXiv:2206.03324v3, p. 14:
"Condition on the good checking event ℰ_ℓ. Then a decentralized queueing system where all queues
follow DAM.converge, converges in at most (99 K L_check / ε)(log N + K) time slots."

Stated pathwise for the epoch auction `epochRun` with general nonnegative weights: some slot
`t ≥ t₀` with `t − t₀ + 1 ≤ (99 K L_check/ε)(log₂ N + K)` (the slots `t₀, …, t`) has
`|R_j(t)| ≤ 1` for every server `j`.

**Formalization Note** `log` is `log₂` (as in eq. (2)). No two queues bid equally at a server in
the epoch (footnote 2, p. 7); at an exact tie a time-dependent tie rule can serve two tied queues
alternately forever, so the system never converges. -/
theorem lemma_3_6 {N K : ℕ} [NeZero N] [NeZero K] (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (rules : TieRules N K) (w : Fin N → Fin K → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (η : Fin N → ℝ) (hη : ∀ i, η i ∈ Set.Ioo (0 : ℝ) (1 / 10 ^ 9))
    (S : ℕ → Fin N → Fin K → Bool) (t0 : ℕ) (ht0 : 1 ≤ t0)
    (hE : GoodChecking ε δ rules (epochRun ε δ rules w η S t0) S t0)
    (hnt : NoBidTies ε δ (epochRun ε δ rules w η S t0) t0) :
    ∃ t, t0 ≤ t ∧
      ((t - t0 + 1 : ℕ) : ℝ) ≤ 99 * K * (Lcheck N K ε δ : ℝ) / ε * (Real.logb 2 N + K) ∧
      ConvergesAt (epochRun ε δ rules w η S t0) t0 t := by sorry

end DecQueueLearning
