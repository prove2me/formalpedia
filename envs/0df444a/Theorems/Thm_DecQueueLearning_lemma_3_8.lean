-- Prove2me | Theorems.Thm_DecQueueLearning_lemma_3_8
-- name    : DecQueueLearning.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:41:35.16285+00:00
-- url     : https://prove2.me/theorems/9f11b323-934d-43a0-9a6a-eaaf5376dc07
-- title:
--   Lemma 3.8 — the converged matching satisfies $\tfrac{1}{16}\varepsilon$-complementary slackness
-- statement:
--   Run the epoch auction with general nonnegative weights $w$ starting at slot $t_0$, and assume the good checking event $\mathcal E_\ell$ holds on the path. If the system converges in a slot $t$ of the converge phase, $t_0\le t\le t_0+L_{\mathrm{conv}}-1$, and $\sigma(i)=J(i,t)$ is the induced matching ($\sigma(i)=j$ iff $i\in R_j(t)$), then there exist $\hat p\in\mathbb R^K$ and $\hat\pi\in\mathbb R^N$ such that $(\sigma,\hat p,\hat\pi)$ satisfies $\tfrac1{16}\varepsilon$-complementary slackness for the weights $w$.
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
--   - reading: the system converges to a matching σ → convergence at a slot t with t₀ ≤ t ≤ t₀ + L_conv − 1 and σ(i) = J(i, t); reason: the induced matching of p. 13; ℰ_ℓ covers the converge phase
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, Lemma 3.8, p.15 (PDF 16)

import Mathlib
import Definitions.Def_DecQueueLearning_Constants
import Definitions.Def_DecQueueLearning_TieRules
import Definitions.Def_DecQueueLearning_Auction
import Definitions.Def_DecQueueLearning_CompSlack

namespace DecQueueLearning

/-- **Lemma 3.8**, Freund–Lykouris–Weng, arXiv:2206.03324v3, p. 15: "Condition on event ℰ_ℓ. If the
queueing system with queues using DAM.converge converges to a matching σ, then there exist a payoff
vector π̂ and a price vector p̂, such that the tuple (σ, p̂, π̂) satisfies (1/16)ε-complementary
slackness."

Stated pathwise for the epoch auction `epochRun` with general nonnegative weights: if the system
converges in a slot `t` of the converge phase, the induced matching `σ(i) = J(i, t)` (`σ(i) = j`
iff `i ∈ R_j(t)`) admits `p̂, π̂` with `(ε/16)`-complementary slackness for the weights `w`. -/
theorem lemma_3_8 {N K : ℕ} [NeZero N] [NeZero K] (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (rules : TieRules N K) (w : Fin N → Fin K → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (η : Fin N → ℝ) (hη : ∀ i, η i ∈ Set.Ioo (0 : ℝ) (1 / 10 ^ 9))
    (S : ℕ → Fin N → Fin K → Bool) (t0 : ℕ) (ht0 : 1 ≤ t0)
    (hE : GoodChecking ε δ rules (epochRun ε δ rules w η S t0) S t0)
    (t : ℕ) (ht0t : t0 ≤ t) (htc : t ≤ t0 + Lconv N K ε δ - 1)
    (hconv : ConvergesAt (epochRun ε δ rules w η S t0) t0 t) :
    ∃ (p : Fin K → ℝ) (π : Fin N → ℝ), IsCompSlack (ε / 16) w
      (fun i => (stateAt (epochRun ε δ rules w η S t0) t0 t i).J) p π := by sorry

end DecQueueLearning
