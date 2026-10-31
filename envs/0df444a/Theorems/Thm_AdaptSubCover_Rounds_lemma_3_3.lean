-- Prove2me | Theorems.Thm_AdaptSubCover_Rounds_lemma_3_3
-- name    : AdaptSubCover.Rounds.lemma_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:42.915365+00:00
-- url     : https://prove2.me/theorems/7b875069-d80f-4989-89ed-a551895059c5
-- title:
--   Lemma 3.3, p. 9 — for α = (8β/δ)(1 + ln(1/δ)) and every phase i ≥ 1, u_i ≤ u_{i−1}/4 + (6/5)u*_i
-- statement:
--   There is an absolute constant $\beta > 0$ with the following property. Let $f$ be monotone submodular with $Q > 0$, $\delta = 2^{-z}$, $\tau = Q(1-\delta)$, $L$ a list built by ParCA, $\mathtt{OPT}$ a feasible adaptive solution, and set $\alpha := \frac{8\beta}{\delta}\,(1 + \ln(1/\delta))$ (§4.3). Then for every phase $i \ge 1$,
--
--   $$u_i \;\le\; \frac{u_{i-1}}{4} + \frac65\, u^*_i,$$
--
--   where $u_i$ is the probability that $\mathtt{NA}$ costs at least $\alpha 2^i$ and $u^*_i$ the probability that $\mathtt{OPT}$ costs at least $2^i$. This is the key lemma: summing it over phases yields Theorem 3.1.
--
--   **Formalization Note.** $\beta$ is the constant "$\beta = O(1)$" of (10), quantified before every instance. No hypothesis on the integrality of $\tau$ is made.
-- source:
--   Ghuge, Gupta, Nagarajan, The Power of Adaptivity for Stochastic Submodular Cover, arXiv:2106.16115v1, p. 9, Lemma 3.3; α from §4.3, p. 15; β from eq. (10), p. 14

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Analysis

namespace AdaptSubCover.Rounds

theorem lemma_3_3 :
    ∃ β : ℝ, 0 < β ∧
      ∀ (U : Type) [Fintype U] [DecidableEq U] (m : ℕ) (I : Instance U m),
        I.Standing → 0 < I.Q →
        ∀ (z : ℕ) (L : List (Fin m)), I.IsGreedyList (fun A => (I.f A : ℝ)) I.Q (I.tau z) Finset.univ L →
        ∀ π : AdaptivePolicy m U, I.Feasible π → ∀ i : ℕ, 1 ≤ i →
          I.uPhase (I.tau z) (8 * β / delta z * (1 + Real.log (1 / delta z))) L i ≤
            I.uPhase (I.tau z) (8 * β / delta z * (1 + Real.log (1 / delta z))) L (i - 1) / 4 +
              6 / 5 * I.uStar π i := by sorry

end AdaptSubCover.Rounds
