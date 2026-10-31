-- Prove2me | Theorems.Thm_DisclosureStatics_Aggregation_lemma_1
-- name    : DisclosureStatics.Aggregation.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:41.84931+00:00
-- url     : https://prove2.me/theorems/0b5f6640-a31b-4d4e-965a-c47a8c58a54a
-- title:
--   Lemma 1 (Monotonicity), p. 21 — an event's value is higher exactly when its probability-adjusted price is lower
-- statement:
--   Assume the standing assumptions, Assumption 1 ($u(x)=(1-e^{-\gamma x})/\gamma$, $\gamma>0$) and Assumption 2 on $(-\infty,1/\gamma)$. Let $\pi$ be a PDS and let $c$ solve (DP-$\pi$). Then for any two events $S_i,S_j\in\pi$ (including the default event $\{s_1\}$),
--   $$V_{S_i}(c)>V_{S_j}(c)\iff \frac{p_{S_i}}{P(S_i)}<\frac{p_{S_j}}{P(S_j)}.$$
--
--   The lemma ranks the events of a disclosure statement by their values using observable prices and probabilities only; it underlies the ranking of events used in Lemma 5 and Proposition 2.
-- source:
--   Burkovskaya & Li, Comparative Profitability of Product Disclosure Statements, SSRN 3532175 (version of February 4, 2020), p. 21, Lemma 1

import Mathlib
import Definitions.Def_DisclosureStatics_Aggregation_Model

namespace DisclosureStatics.Aggregation

/-- Lemma 1 (Monotonicity), p. 21. -/
theorem lemma_1 {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (M : Market Ω) (hM : M.Standing) (γ : ℝ) (hγ : 0 < γ)
    (φ : ℝ → ℝ) (hφ : AggregationAverse φ (Set.Iio (1 / γ)))
    (π : PDS Ω) (hπ : IsPDS M π) (c : Ω → ℝ) (hc : IsDemand M (cara γ) φ π c) :
    ∀ S ∈ π.parts, ∀ S' ∈ π.parts,
      (V M (cara γ) S' c < V M (cara γ) S c ↔ rE M S < rE M S') := by sorry
end DisclosureStatics.Aggregation
