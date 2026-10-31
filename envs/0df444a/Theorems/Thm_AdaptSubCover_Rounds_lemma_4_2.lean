-- Prove2me | Theorems.Thm_AdaptSubCover_Rounds_lemma_4_2
-- name    : AdaptSubCover.Rounds.lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:50.170481+00:00
-- url     : https://prove2.me/theorems/5a3162bf-fc5e-473e-8145-815461a12749
-- title:
--   Lemma 4.2, p. 11 — for a good scale θ some 𝒯_θ ⊆ 𝒳∖𝒮 of cost ≤ (144/θ)·2^i gains (θQ/6)·r*_{iθ}/P(ℰ_θ) in expectation
-- statement:
--   Let $f$ be monotone submodular with $Q > 0$, let $\mathcal S$ be a set of items, $\mathtt{OPT}$ an adaptive solution, $i \ge 0$, and let $\theta = 2^{-j}$ be a good scale. Then there is a set of items $\mathcal T_\theta \subseteq \mathcal X \setminus \mathcal S$ with $c(\mathcal T_\theta) \le \frac{144}{\theta}\cdot 2^i$ such that
--
--   $$\mathbb E_{S \sim \mathcal E_\theta}\,\mathbb E_{T_\theta \sim \mathcal T_\theta}\big[f(S \cup T_\theta) - f(S)\big] \;\ge\; \frac{\theta Q}{6}\cdot\frac{r^*_{i\theta}}{\Pr(\mathcal E_\theta)}. \tag{6}$$
--
--   Here $S \sim \mathcal E_\theta$ is the realization of $\mathcal S$ conditioned on lying in scale $\theta$, and $T_\theta$ is the (independent) realization of $\mathcal T_\theta$. The lemma converts the adaptive progress of $\mathtt{OPT}$ within budget $2^i$ into a fixed set of items, scale by scale; it feeds Lemma 4.3.
--
--   **Formalization Note.** The lemma is stated for an arbitrary item set $\mathcal S$ and arbitrary adaptive $\pi$ in the role of $\mathtt{OPT}$ (the paper's $\mathcal S$ is the time-$t$ prefix of ParCA's list). The conditional expectation is $\mathbb E[\,\cdot\,\mathbf 1_{\mathcal E_\theta}]/\Pr(\mathcal E_\theta)$; a good scale has $\Pr(\mathcal E_\theta) > 0$.
-- source:
--   Ghuge, Gupta, Nagarajan, The Power of Adaptivity for Stochastic Submodular Cover, arXiv:2106.16115v1, p. 11, Lemma 4.2, eq. (6)

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Analysis

namespace AdaptSubCover.Rounds

theorem lemma_4_2 {U : Type} [Fintype U] [DecidableEq U] {m : ℕ} (I : Instance U m) (hI : I.Standing) (hQ : 0 < I.Q)
    (π : AdaptivePolicy m U) (i j : ℕ) (S : Finset (Fin m)) (hgood : I.Good π i j S) :
    ∃ T ⊆ Finset.univ \ S, ((∑ e ∈ T, I.c e : ℕ) : ℝ) ≤ 144 / (2⁻¹ : ℝ) ^ j * 2 ^ i ∧
      I.condE (I.InScale j S)
          (fun ω => (I.f (S.image ω ∪ T.image ω) : ℝ) - I.f (S.image ω)) ≥
        (2⁻¹ : ℝ) ^ j * I.Q / 6 * (I.rStar π i j S / I.P (I.InScale j S)) := by sorry

end AdaptSubCover.Rounds
