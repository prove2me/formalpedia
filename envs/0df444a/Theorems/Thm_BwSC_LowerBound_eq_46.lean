-- Prove2me | Theorems.Thm_BwSC_LowerBound_eq_46
-- name    : BwSC.LowerBound.eq_46
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:35:22.752405+00:00
-- url     : https://prove2.me/theorems/ed25a476-0dc9-4e0d-a4b1-bdbec598a977
-- title:
--   Eq. (46), pp. 74–75 — p̄^(1) ≥ ((2−√2)/4)·(K−r(S,K))/((q(S,K)+2)²K) (q ≥ 1)
-- statement:
--   Let $K>1$, $T\ge2K$, $\pi\in\Pi_S$, $q=q(S,K)\ge1$, $r=r(S,K)$, and let $\overline{p^{(1)}}=\frac1{(q+2)K}\sum_{j\in[q+2]}\sum_{k\in[K]}\mathbb P^{(1)}_{j,k}(E^{(1)}_{j,k})$ be the average bad-event probability of the first class. Then
--   $$\overline{p^{(1)}}\ \ge\ \frac{2-\sqrt2}{4}\cdot\frac{K-r}{(q+2)^2K}.$$
--
--   With Lemma 9 this gives the first term of Theorem 2: the average regret over $\Phi_1$ is at least $R_{\rm bad}(S,K,T)$ times this quantity.
--
--   **Formalization Note** The end-to-end conclusion of the chain (46) is stated. $q\ge1$ is assumed because the first-class construction is undefined at $q=0$.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 74, eq. (46) (App. J.5)

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound

/-- Eq. (46), pp. 74–75: `p̄^{(1)} ≥ ((2 - √2)/4) · (K - r(S,K))/((q(S,K)+2)²K)`.
Stated for `q(S,K) ≥ 1`. -/
theorem eq_46 {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) (hq : 1 ≤ qIdx S K) :
    (2 - Real.sqrt 2) / 4 * (((K : ℝ) - (rIdx S K : ℝ)) / (((qIdx S K : ℝ) + 2) ^ 2 * K)) ≤
      pbar1 π S T := by sorry

end BwSC.LowerBound
