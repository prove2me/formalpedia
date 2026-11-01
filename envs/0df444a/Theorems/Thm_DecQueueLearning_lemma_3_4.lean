-- Prove2me | Theorems.Thm_DecQueueLearning_lemma_3_4
-- name    : DecQueueLearning.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:41:11.699327+00:00
-- url     : https://prove2.me/theorems/e33b8f7d-c95d-44b2-97f9-5f032bd4b206
-- title:
--   Lemma 3.4 — matched servers do not become unmatched
-- statement:
--   Run the epoch auction with general nonnegative weights $w$ starting at slot $t_0$, and assume the good checking event $\mathcal E_\ell$ holds on the path. If at a slot $t\ge t_0$ every server receives at most one request, $|R_j(t)|\le1$ for all $j$, then
--   $$
--   R_j(t')=R_j(t)\qquad\text{for all servers } j \text{ and all slots } t<t'\le t_0+L_{\mathrm{epoch}}-1 .
--   $$
--   Once the system has converged, the matching stays fixed for the rest of the epoch.
--
--   Differences from the source:
--   - encoding: queues 𝒩 = [N], servers 𝒦 = [K], no request ⊥ → Fin N, Fin K (paper index = Lean index + 1), Option with none for ⊥; reason: Lean convention; same instances
--   - reading: log in eq. (2) (base unstated) → log₂ (Real.logb 2) in ξ, L_conv and the stated bound; reason: the proof of Lemma 3.6 (D.5, p. 42) bounds ⌈68pK/ε⌉(L_check + 1) by 91 (log N) K L_check/ε with p < log N halvings, which needs base 2
--   - reading: a lower bound δ on the nonzero rates, µᵢⱼ ∈ {0} ∪ [δ, 1] → 0 < δ < 1; reason: eq. (2) uses ln(1 − δ), undefined at δ = 1
--   - reading: Algorithm 2, line 1: pᵢⱼ(t₀) ← 0, while line 6 at t = t₀ reads pᵢⱼ(t₀ − 1) → pᵢⱼ(t₀ − 1) = 0 and τᵢ(t₀ − 1) = t₀ − 1; reason: the prices read in the first slot of the epoch are the initial ones
--   - reading: Algorithm 2, line 13: 'Price updates for some server j' → only line 8 sets τᵢ(t) ← t; line 10 leaves τᵢ unchanged; reason: after line 10 every payoff is nonpositive and the prices are frozen, so the queue stays at ⊥ whichever way τᵢ moves; same process
--   - reading: ties broken arbitrarily (footnote 2, p. 7; arg max in Algorithm 2, line 6) → every tie rule (TieRules), which may depend on the queue or server and on the slot, measurable in the bids; reason: measurability is what makes the queue lengths random variables
--   - generalization: weights wᵢⱼ = µ̃ᵢⱼ Qᵢ(t₀) of an epoch of the process, started at t₀ = (ℓ − 1)L_epoch + 1 → any nonnegative weights w, any start t₀ ≥ 1, any perturbations ηᵢ ∈ (0, 10⁻⁹), any service-coin path S; reason: p. 13: the results of §3.3 'hold for general wᵢⱼ'; the epoch of DAM.K is the instance w = µQ(t₀) (proved by rfl in the sanity file)
--   - reading: Algorithm 3: for t = t_s to t_e − 1 → DAM.COMMIT requests in every slot of [t_s, t_e], inclusive of t_e; reason: Algorithms 1 and 4 call it on [t₀ + L_conv, t₀ + L_epoch − 1]; p. 20 ('keeps requesting … in [t₀ + L_conv, t₀ + L_epoch − 1]') and Lemma 4.1 need every slot
--   - encoding: ℰ_ℓ requires S_{I(j,t′),j}(t′) = 1 → a slot with I(j, t′) = ⊥ counts as a success; reason: the paper sets µ_{⊥,j} = 1 (p. 6)
--   - reading: t′ > t → t < t′ ≤ t₀ + L_epoch − 1; reason: the next epoch restarts the auction from fresh prices, so the lemma speaks about the rest of the epoch (proof in D.3, p. 40)
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, Lemma 3.4, p.13 (PDF 14)

import Mathlib
import Definitions.Def_DecQueueLearning_Constants
import Definitions.Def_DecQueueLearning_TieRules
import Definitions.Def_DecQueueLearning_Auction

namespace DecQueueLearning

/-- **Lemma 3.4** (matched servers do not become unmatched), Freund–Lykouris–Weng,
arXiv:2206.03324v3, p. 13: "Condition on the good checking event ℰ_ℓ and assume that at time slot
t, |R_j(t)| ≤ 1 for all j ∈ 𝒦. Then R_j(t′) = R_j(t), ∀j ∈ 𝒦, t′ > t."

Stated pathwise for the epoch auction `epochRun` with general nonnegative weights `w` (p. 13: the
results of §3.3 hold for general `wᵢⱼ`), arbitrary perturbations `ηᵢ ∈ (0, 10⁻⁹)`, arbitrary tie
rules and an arbitrary path `S` of service coins satisfying the good checking event.

**Formalization Note** `t′` ranges over the rest of the epoch, `t < t′ ≤ t₀ + L_epoch − 1` (the
next epoch restarts the auction). The epoch start `t₀ ≥ 1` is arbitrary. -/
theorem lemma_3_4 {N K : ℕ} [NeZero N] [NeZero K] (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (rules : TieRules N K) (w : Fin N → Fin K → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (η : Fin N → ℝ) (hη : ∀ i, η i ∈ Set.Ioo (0 : ℝ) (1 / 10 ^ 9))
    (S : ℕ → Fin N → Fin K → Bool) (t0 : ℕ) (ht0 : 1 ≤ t0)
    (hE : GoodChecking ε δ rules (epochRun ε δ rules w η S t0) S t0)
    (t : ℕ) (ht0t : t0 ≤ t) (hconv : ConvergesAt (epochRun ε δ rules w η S t0) t0 t)
    (t' : ℕ) (htt' : t < t') (ht' : t' ≤ t0 + Lepoch N K ε δ - 1) :
    ∀ j, R (epochRun ε δ rules w η S t0) t0 j t' = R (epochRun ε δ rules w η S t0) t0 j t := by sorry

end DecQueueLearning
