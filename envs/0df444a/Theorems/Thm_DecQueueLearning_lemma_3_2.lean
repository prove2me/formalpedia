-- Prove2me | Theorems.Thm_DecQueueLearning_lemma_3_2
-- name    : DecQueueLearning.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:41:43.001399+00:00
-- url     : https://prove2.me/theorems/8639daa6-de22-43f4-b859-1797a555370e
-- title:
--   Lemma 3.2 — DAM.CONVERGE yields a $(1-\varepsilon/16)$-approximate max-weight matching
-- statement:
--   Run the epoch auction with general nonnegative weights $w$ starting at slot $t_0$, assume the good checking event $\mathcal E_\ell$ holds on the path and that no two queues send equal bids to one server in the epoch. Let $\sigma(i)=J(i,t_0+L_{\mathrm{conv}}-1)$ be the server returned by DAM.CONVERGE (line 15). Then $\sigma$ is a matching (for $i\ne i'$, $\sigma(i)=\bot$ or $\sigma(i)\ne\sigma(i')$), and
--   $$
--   \sum_{i=1}^N w_{i,\sigma(i)}\ \ge\ \Big(1-\frac{\varepsilon}{16}\Big)\max_{\phi\in\mathcal S}\sum_{i=1}^N\sum_{j=1}^K\phi_{i,j}w_{i,j},
--   $$
--   with $w_{i,\bot}=0$ and $\mathcal S=\Phi$ the feasible set of (Primal). This is what lets the commit phase run near a max-weight schedule.
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
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, Lemma 3.2, p.13 (PDF 14)

import Mathlib
import Definitions.Def_DecQueueLearning_Constants
import Definitions.Def_DecQueueLearning_TieRules
import Definitions.Def_DecQueueLearning_Auction
import Definitions.Def_DecQueueLearning_CompSlack

namespace DecQueueLearning

/-- **Lemma 3.2**, Freund–Lykouris–Weng, arXiv:2206.03324v3, p. 13: "Assume that all queues follow
DAM.converge in an epoch ℓ with time slots [t₀, t₀ + L_conv − 1] and let 𝒮 be the set of feasible
solutions in (Primal). Under the good checking event ℰ_ℓ, it holds that σ is a matching where for
i ≠ i′, either σ(i) = ⊥ or σ(i) ≠ σ(i′) and
Σᵢ w_{i,σ(i)} ≥ (1 − ε/16) max_{ϕ∈𝒮} Σᵢ Σⱼ ϕᵢⱼ wᵢⱼ."

Stated pathwise for the epoch auction `epochRun` with general nonnegative weights; `σ` is the
output `J(i, t₀ + L_conv − 1)` of Algorithm 2 (line 15), and `w_{i,⊥} = 0`.

**Formalization Note** No two queues bid equally at a server in the epoch (footnote 2, p. 7); at
an exact tie a time-dependent tie rule can serve two tied queues alternately, and both then commit
to the same server, so `σ` is not a matching. -/
theorem lemma_3_2 {N K : ℕ} [NeZero N] [NeZero K] (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (rules : TieRules N K) (w : Fin N → Fin K → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (η : Fin N → ℝ) (hη : ∀ i, η i ∈ Set.Ioo (0 : ℝ) (1 / 10 ^ 9))
    (S : ℕ → Fin N → Fin K → Bool) (t0 : ℕ) (ht0 : 1 ≤ t0)
    (hE : GoodChecking ε δ rules (epochRun ε δ rules w η S t0) S t0)
    (hnt : NoBidTies ε δ (epochRun ε δ rules w η S t0) t0) :
    IsMatching (committed ε δ (epochRun ε δ rules w η S t0) t0) ∧
      (1 - ε / 16) * maxWeight w ≤
        ∑ i, selWeight w (committed ε δ (epochRun ε δ rules w η S t0) t0) i := by sorry

end DecQueueLearning
