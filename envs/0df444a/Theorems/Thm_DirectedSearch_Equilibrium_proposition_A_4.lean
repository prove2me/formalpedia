-- Prove2me | Theorems.Thm_DirectedSearch_Equilibrium_proposition_A_4
-- name    : DirectedSearch.Equilibrium.proposition_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:12.174626+00:00
-- url     : https://prove2.me/theorems/1b769259-c16a-4207-80ec-99ada456025c
-- title:
--   Proposition A.4, p. 36 — the best-response iteration from 0 reaches the equilibrium after O(|Θ|) iterations
-- statement:
--   There is a universal constant $C$ such that the following holds. Let a market with finite type sets $\mathcal M$, $\mathcal W$ satisfy the standing assumptions, let $\lambda_m(w),\lambda_w(m)\ge0$ be assortments, and let $\tau^{(0)}\equiv 0,\tau^{(1)},\tau^{(2)},\dots$ be a best-response sequence (each type's threshold in $\tau^{(k+1)}$ solves its own equation $t=\bar u_\theta(t)$ against the opposite side's thresholds in $\tau^{(k)}$). Put $N=C\,|\Theta|$ with $|\Theta|=|\mathcal M|+|\mathcal W|$. Then
--   1. $\tau^{(N)}$ is a fixed point of the best-response map: every type's threshold in $\tau^{(N)}$ solves its own equation against the opposite thresholds in $\tau^{(N)}$ itself;
--   2. the iteration has stopped: $\tau^{(n)}=\tau^{(N)}$ for every $n\ge N$.
--
--   In words, iterating the best-response map $O(|\Theta|)$ times from the all-zero profile finds the equilibrium profile of thresholds.
--
--   **Formalization Note.** Only the computational clause of Proposition A.4 is stated; its uniqueness clause is the goal theorem (Proposition 3.1, item 1), and the equivalence "up to Lemma A.2" concerns the agents' Markov decision process, which is not formalized. $O(|\Theta|)$ is encoded with a constant $C$ chosen before the market (uniform over all markets). A best-response sequence exists for every market by Lemma A.3, so the statement is not vacuous.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 36, Proposition A.4 (second sentence); proof pp. 36–37

import Mathlib
import Definitions.Def_DirectedSearch_Equilibrium_Setting

namespace DirectedSearch.Equilibrium
theorem proposition_A_4 :
    ∃ C : ℕ, ∀ {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
      (mk : Market M W), mk.Standing →
      ∀ (lamM : M → W → ℝ) (lamW : W → M → ℝ),
        (∀ m w, 0 ≤ lamM m w) → (∀ w m, 0 ≤ lamW w m) →
        ∀ seq : ℕ → (M → ℝ) × (W → ℝ), IsBRSequence mk lamM lamW seq →
          IsBRStep mk lamM lamW (seq (C * (Fintype.card M + Fintype.card W)))
              (seq (C * (Fintype.card M + Fintype.card W))) ∧
            ∀ n, C * (Fintype.card M + Fintype.card W) ≤ n →
              seq n = seq (C * (Fintype.card M + Fintype.card W)) := by sorry
end DirectedSearch.Equilibrium
