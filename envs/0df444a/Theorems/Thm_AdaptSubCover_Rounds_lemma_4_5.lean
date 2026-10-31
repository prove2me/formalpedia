-- Prove2me | Theorems.Thm_AdaptSubCover_Rounds_lemma_4_5
-- name    : AdaptSubCover.Rounds.lemma_4_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:45.680728+00:00
-- url     : https://prove2.me/theorems/27daa0b9-6bd1-4f67-92c3-4688d55ff8a3
-- title:
--   Lemma 4.5, p. 15 — along any decision path Π of NA, G(Π) ≤ 1 + ln(1/δ)
-- statement:
--   Let $f$ be monotone submodular and integer valued with $Q > 0$, $\delta = 2^{-z}$, $\tau = Q(1-\delta)$, $L$ ParCA's greedy list, $\alpha > 0$ and $i \ge 1$. For every decision path $\Pi$ of the non-adaptive strategy $\mathtt{NA}$,
--
--   $$G(\Pi) \;\le\; 1 + \ln(1/\delta),$$
--
--   where $G(\Pi)$ is the phase-$i$ weighted sum of relative marginal gains defined in (14). Taking expectations over decision paths gives the upper bound (15) on the total gain $G$.
--
--   **Formalization Note.** $V_0$ is $f(\emptyset)$, the value of $f$ before the first probe (the paper's proof writes $V_0 = 0$; the statement is unaffected).
-- source:
--   Ghuge, Gupta, Nagarajan, The Power of Adaptivity for Stochastic Submodular Cover, arXiv:2106.16115v1, p. 15, Lemma 4.5; G(Π) from eq. (14)

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Analysis

namespace AdaptSubCover.Rounds

theorem lemma_4_5 {U : Type} [Fintype U] [DecidableEq U] {m : ℕ} (I : Instance U m) (hI : I.Standing) (hQ : 0 < I.Q)
    (z : ℕ) (L : List (Fin m)) (hL : I.IsGreedyList (fun A => (I.f A : ℝ)) I.Q (I.tau z) Finset.univ L)
    (α : ℝ) (hα : 0 < α) (i : ℕ) (hi : 1 ≤ i) (ω : Fin m → U) :
    I.Gpath (I.tau z) α L i ω ≤ 1 + Real.log (1 / delta z) := by sorry

end AdaptSubCover.Rounds
