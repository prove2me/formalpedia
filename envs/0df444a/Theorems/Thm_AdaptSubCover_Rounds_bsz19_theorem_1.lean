-- Prove2me | Theorems.Thm_AdaptSubCover_Rounds_bsz19_theorem_1
-- name    : AdaptSubCover.Rounds.bsz19_theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:54.872973+00:00
-- url     : https://prove2.me/theorems/9de3f583-f554-4520-a8e7-b8bc9c03bc4e
-- title:
--   [BSZ19, Theorem 1], quoted p. 11 — the adaptivity gap of stochastic monotone submodular maximization under a budget is at most 2
-- statement:
--   Let $g : 2^U \to \mathbb R_{\ge 0}$ be non-negative, monotone and submodular, let $\mathcal X_1, \dots, \mathcal X_m$ be independent items realizing to elements of $U$, with costs $c_i$, let $\mathcal A$ be a set of allowed items and $B$ a budget. If $\pi$ is an adaptive solution that probes only allowed items and whose every decision path has total cost at most $B$, then there is a fixed set $\mathcal T \subseteq \mathcal A$ with $c(\mathcal T) \le B$ such that
--
--   $$\mathbb E\big[g(\text{realization of the items probed by } \pi)\big] \;\le\; 2\cdot \mathbb E_{T \sim \mathcal T}[g(T)].$$
--
--   This is the statement "the adaptivity gap for stochastic submodular maximization is at most 2" of Bradac, Singla and Zuzic, used in the proof of Lemma 4.2 with $g = f_S$ and the items $\mathcal X \setminus \mathcal S$.
--
--   **Formalization Note.** This is a cited result ([BSZ19], Theorem 1, for monotone submodular functions under prefix-closed constraints, here a knapsack budget). The budget is required on every decision path, including those of probability zero.
-- source:
--   Ghuge, Gupta, Nagarajan, The Power of Adaptivity for Stochastic Submodular Cover, arXiv:2106.16115v1, p. 11, paragraph 'Constrained stochastic submodular maximization', citing [BSZ19] Bradac, Singla, Zuzic, (Near) Optimal Adaptivity Gaps for Stochastic Multi-Value Probing, APPROX/RANDOM 2019, Theorem 1

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Model

namespace AdaptSubCover.Rounds

theorem bsz19_theorem_1 {U : Type} [Fintype U] [DecidableEq U] {m : ℕ} (I : Instance U m)
    (hp0 : ∀ i u, 0 ≤ I.p i u) (hp1 : ∀ i, ∑ u, I.p i u = 1)
    (g : Finset U → ℝ) (hg0 : ∀ A, 0 ≤ g A) (hgm : Monotone g)
    (hgs : NonmonotoneSubmod.Shared.Submodular g)
    (avail : Finset (Fin m)) (B : ℝ) (π : AdaptivePolicy m U)
    (hπ : ∀ ω, (π.run ω).items ⊆ avail ∧ (I.costOf (π.run ω) : ℝ) ≤ B) :
    ∃ T ⊆ avail, ((∑ e ∈ T, I.c e : ℕ) : ℝ) ≤ B ∧
      I.E (fun ω => g (π.run ω).realized) ≤ 2 * I.E (fun ω => g (T.image ω)) := by sorry

end AdaptSubCover.Rounds
