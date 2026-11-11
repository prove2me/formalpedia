-- Prove2me | Theorems.Thm_DecQueueLearning_lemma_3_7
-- name    : DecQueueLearning.lemma_3_7
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T14:41:11.480717+00:00
-- url     : https://prove2.me/theorems/6486e4f3-6448-4fee-89a1-73cf6068b626
-- title:
--   Lemma 3.7 — $\alpha$-complementary slackness gives a $(1-\alpha)$-approximate max-weight matching
-- statement:
--   Let $\alpha>0$, let $w\in\mathbb R^{N\times K}$ be weights (with $w_{i,\bot}=0$) and let $\sigma$ be a matching. If there exist a price vector $\hat p\in\mathbb R^K$ and a payoff vector $\hat\pi\in\mathbb R^N$ such that $(\sigma,\hat p,\hat\pi)$ satisfies $\alpha$-complementary slackness, then
--   $$
--   \sum_{i=1}^N w_{i,\sigma(i)}\ \ge\ (1-\alpha)\max_{\phi\in\Phi}\sum_{i=1}^N\sum_{j=1}^K w_{i,j}\phi_{i,j}.
--   $$
--   This is the duality step that turns the prices of the decentralized auction into a weight guarantee.
--
--   Differences from the source:
--   - encoding: queues 𝒩 = [N], servers 𝒦 = [K], no request ⊥ → Fin N, Fin K (paper index = Lean index + 1), Option with none for ⊥; reason: Lean convention; same instances
--   - generalization: the weights of the queueing system (nonnegative) and N, K ≥ 1 → any real weights w and any N, K; reason: the statement specializes to the paper's weights; it is the paper's claim for each of them
--   - encoding: max over Φ; π̂ᵢ = max(maxⱼ wᵢⱼ − p̂ⱼ, 0) → sSup of the objective over Φ; π̂ᵢ the greatest element of {0} ∪ {wᵢⱼ − p̂ⱼ}; reason: Φ is compact and nonempty, so the supremum is the maximum; same instances
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, Lemma 3.7, p.14 (PDF 15)

import Mathlib
import Definitions.Def_DecQueueLearning_CompSlack

namespace DecQueueLearning

/-- **Lemma 3.7**, Freund–Lykouris–Weng, arXiv:2206.03324v3, p. 14: "If for a matching σ, there
exist price p̂ and payoff π̂ such that the tuple (σ, p̂, π̂) satisfies α-complementary slackness, then
Σᵢ w_{i,σ(i)} ≥ (1 − α) max_{ϕ∈Φ} Σᵢ Σⱼ wᵢⱼ ϕᵢⱼ."

For every `α > 0` (p. 14: "for a fixed α > 0") and real weights `w`, with `w_{i,⊥} = 0`. -/
theorem lemma_3_7 {N K : ℕ} (α : ℝ) (hα : 0 < α) (w : Fin N → Fin K → ℝ)
    (σ : Fin N → Option (Fin K)) (hσ : IsMatching σ) (p : Fin K → ℝ) (π : Fin N → ℝ)
    (h : IsCompSlack α w σ p π) :
    (1 - α) * maxWeight w ≤ ∑ i, selWeight w σ i := by sorry

end DecQueueLearning
