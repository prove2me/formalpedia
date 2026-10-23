-- Prove2me | Theorems.Thm_AdaptSubCover_Rounds_lemma_4_4
-- name    : AdaptSubCover.Rounds.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:55.506095+00:00
-- url     : https://prove2.me/theorems/778de25e-c50a-4591-829e-a9c1379fea0f
-- title:
--   Lemma 4.4, p. 14 — Σ_{θ>δ, good} r*_{iθ} ≥ u_i − 6u*_i/5 (for non-integral τ)
-- statement:
--   Let $f$ be monotone submodular with $Q > 0$, $\delta = 2^{-z}$, $\tau = Q(1-\delta)$, $L$ ParCA's greedy list, $\mathtt{OPT}$ a feasible adaptive solution, $\alpha > 0$, $i \ge 1$, and fix a time $t \in [\alpha 2^{i-1}, \alpha 2^i)$, with $\mathcal S$ the items chosen until time $t$. If $\tau$ is not an integer, then
--
--   $$\sum_{\theta > \delta,\ \text{good}} r^*_{i\theta} \;\ge\; u_i - \frac{6\,u^*_i}{5}.$$
--
--   Together with Lemma 4.3 and the greedy choice this gives the lower bound (13) on the total gain $G$ in phase $i$.
--
--   **Formalization Note.** The proof's step (12) uses the equivalence of Lemma 4.1, which fails when $f(S) = \tau$; the hypothesis that $\tau$ is not an integer is therefore added, as in the Lean statement of Lemma 4.1. (Lemma 3.3, stated with an unspecified constant $\beta$, carries no such hypothesis.)
-- source:
--   Ghuge, Gupta, Nagarajan, The Power of Adaptivity for Stochastic Submodular Cover, arXiv:2106.16115v1, p. 14, Lemma 4.4

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Analysis

namespace AdaptSubCover.Rounds

theorem lemma_4_4 {U : Type} [Fintype U] [DecidableEq U] {m : ℕ} (I : Instance U m) (hI : I.Standing) (hQ : 0 < I.Q)
    (z : ℕ) (hτ : ∀ n : ℕ, (n : ℝ) ≠ I.tau z)
    (L : List (Fin m)) (hL : I.IsGreedyList (fun A => (I.f A : ℝ)) I.Q (I.tau z) Finset.univ L)
    (π : AdaptivePolicy m U) (hπ : I.Feasible π)
    (α : ℝ) (hα : 0 < α) (i : ℕ) (hi : 1 ≤ i)
    (t : ℝ) (ht1 : α * 2 ^ (i - 1) ≤ t) (ht2 : t < α * 2 ^ i) :
    I.goodSum π i z (I.prefixAt L t) ≥
      I.uPhase (I.tau z) α L i - 6 / 5 * I.uStar π i := by sorry

end AdaptSubCover.Rounds
