-- Prove2me | Theorems.Thm_AdaptSubCover_Rounds_lemma_4_3
-- name    : AdaptSubCover.Rounds.lemma_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:38.720997+00:00
-- url     : https://prove2.me/theorems/a58c1ff5-3b94-4c4b-b40f-77d47432aa6b
-- title:
--   Lemma 4.3, p. 13 — some 𝒯 ⊆ 𝒳∖𝒮 of cost ≤ (144/δ)·2^i has E[g(T)] ≥ (1/6)·Σ_{θ>δ, good} r*_{iθ}
-- statement:
--   Let $f$ be monotone submodular with $Q > 0$, $\delta = 2^{-z}$, $\tau = Q(1-\delta)$, $\mathtt{OPT}$ an adaptive solution and $i \ge 0$. For any set of items $\mathcal S \subseteq \mathcal X$ there is a set $\mathcal T \subseteq \mathcal X \setminus \mathcal S$ of total cost at most $\frac{144}{\delta}\cdot 2^i$ with
--
--   $$\mathbb E_{T \sim \mathcal T}[g(T)] \;\ge\; \frac16 \sum_{\theta > \delta,\ \text{good}} r^*_{i\theta},$$
--
--   where $g(T) = \sum_{S \sim \mathcal S : f(S) < \tau} \Pr(\mathcal S = S)\,\frac{f(S \cup T) - f(S)}{Q - f(S)}$ is the function (5) and the sum runs over the good scales $\theta = 2^{-j} > \delta$. Combined with averaging, it lower-bounds the best score (10) in phase $i$.
--
--   **Formalization Note.** $g$ is taken in the second form of (5) (sum over $f(S) < \tau$), which equals the first form (sum over scales $\theta > \delta$).
-- source:
--   Ghuge, Gupta, Nagarajan, The Power of Adaptivity for Stochastic Submodular Cover, arXiv:2106.16115v1, p. 13, Lemma 4.3; g from eq. (5), p. 11

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Analysis

namespace AdaptSubCover.Rounds

theorem lemma_4_3 {U : Type} [Fintype U] [DecidableEq U] {m : ℕ} (I : Instance U m) (hI : I.Standing) (hQ : 0 < I.Q)
    (z : ℕ) (π : AdaptivePolicy m U) (i : ℕ) (S : Finset (Fin m)) :
    ∃ T ⊆ Finset.univ \ S, ((∑ e ∈ T, I.c e : ℕ) : ℝ) ≤ 144 / delta z * 2 ^ i ∧
      I.gExp (I.tau z) S T ≥ 1 / 6 * I.goodSum π i z S := by sorry

end AdaptSubCover.Rounds
