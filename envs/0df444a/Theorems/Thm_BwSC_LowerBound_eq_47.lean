-- Prove2me | Theorems.Thm_BwSC_LowerBound_eq_47
-- name    : BwSC.LowerBound.eq_47
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:35:07.269757+00:00
-- url     : https://prove2.me/theorems/41636525-8f35-4d0d-8147-bc55ada45886
-- title:
--   Eq. (47), p. 75 — p̄^(2) ≥ ((2−√2)/4)·1/(q(S,K)+2)²
-- statement:
--   Let $K>1$, $T\ge2K$, $\pi\in\Pi_S$, $q=q(S,K)$, and let $\overline{p^{(2)}}=\frac1{(q+2)K}\sum_{j\in[q+2]}\sum_{k\in[K]}\mathbb P^{(2)}_{j,k}(E^{(2)}_{j,k})$. Then
--   $$\overline{p^{(2)}}\ \ge\ \frac{2-\sqrt2}{4}\cdot\frac{1}{(q+2)^2}.$$
--
--   With Lemma 11 this gives the second term of Theorem 2.
--
--   **Formalization Note** The end-to-end conclusion of the chain (47) is stated.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, pp. 74–75, eq. (47) (App. J.5)

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound

/-- Eq. (47), p. 75: `p̄^{(2)} ≥ ((2 - √2)/4) · 1/(q(S,K)+2)²`. -/
theorem eq_47 {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) :
    (2 - Real.sqrt 2) / 4 * (1 / ((qIdx S K : ℝ) + 2) ^ 2) ≤ pbar2 π S T := by sorry

end BwSC.LowerBound
