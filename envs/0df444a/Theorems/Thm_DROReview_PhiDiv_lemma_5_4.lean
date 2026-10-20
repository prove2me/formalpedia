-- Prove2me | Theorems.Thm_DROReview_PhiDiv_lemma_5_4
-- name    : DROReview.PhiDiv.lemma_5_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T21:17:40.134395+00:00
-- url     : https://prove2.me/theorems/13de0d22-f8a4-4d1a-8e9d-59c875bc7bbe
-- title:
--   Lemma 5.4 — corrected divergence chain and ambiguity-ball inclusions
-- statement:
--   Let $P,P_0$ be probability measures on a measurable space and let $\varepsilon\ge0$. For the variation, Hellinger, Kullback–Leibler, and J-divergences of Table 1, the valid part of Lemma 5.4 is
--
--   $$
--   \frac14\bigl(\mathfrak D^{\phi_v}(P,P_0)\bigr)^2
--   \le\mathfrak D^{\phi_h}(P,P_0)
--   \le\mathfrak D^{\phi_{\mathrm{kl}}}(P,P_0)
--   \le\mathfrak D^{\phi_j}(P,P_0),
--   $$
--
--   and, for the associated ambiguity balls,
--
--   $$
--   \mathcal P^{\phi_j}(P_0;\varepsilon)
--   \subseteq\mathcal P^{\phi_{\mathrm{kl}}}(P_0;\varepsilon)
--   \subseteq\mathcal P^{\phi_h}(P_0;\varepsilon)
--   \subseteq\mathcal P^{\phi_v}(P_0;2\sqrt\varepsilon).
--   $$
--
--   Thus a J, KL, or Hellinger constraint supplies a variation-distance guarantee with the stated radius. The three separate divergence comparisons are the mission's milestones.
--
--   **Formalization Note** The paper also prints $\mathfrak D^{\phi_j}\le\mathfrak D^{\phi_{\mathrm{ca}^2}}$ and the corresponding first inclusion in (5.11). Both are false and are omitted. On $\Xi=\{1,2\}$, $P_0=(1/2,1/2)$, $P=(0,1)$, J-divergence is $+\infty$ while the order-two χ-divergence is $1$; hence the claimed comparison and inclusion fail. Variation is the full $L^1$ divergence, and all divergences and radii use extended nonnegative values.
-- source:
--   Rahimian, Mehrotra, Distributionally Robust Optimization: A Review, arXiv:1908.05659v1 (2019), p. 34, Lemma 5.4, equations (5.10)–(5.11); p. 35, footnote 18

import Definitions.Def_DROReview_PhiDiv_phiDiv
import Definitions.Def_DROReview_PhiDiv_generators
import Definitions.Def_DROReview_PhiDiv_ball

namespace DROReview.PhiDiv

open MeasureTheory

/-- Lemma 5.4, (5.10)–(5.11), p. 34, with the two false χ² clauses omitted.
The omitted inequality and inclusion fail on two-point probability spaces. -/
theorem lemma_5_4 {Ξ : Type*} [MeasurableSpace Ξ]
    (P P₀ : ProbabilityMeasure Ξ) (ε : ENNReal) :
    ((1 / 4 : ENNReal) *
        (phiDiv phiV P P₀) ^ 2 ≤
        phiDiv phiH P P₀) ∧
    (phiDiv phiH P P₀ ≤
      phiDiv phiKL P P₀) ∧
    (phiDiv phiKL P P₀ ≤
      phiDiv phiJ P P₀) ∧
    (phiBall phiJ P₀ ε ⊆ phiBall phiKL P₀ ε) ∧
    (phiBall phiKL P₀ ε ⊆ phiBall phiH P₀ ε) ∧
    (phiBall phiH P₀ ε ⊆ phiBall phiV P₀
      (2 * ε ^ (1 / (2 : ℝ)))) := by sorry

end DROReview.PhiDiv
