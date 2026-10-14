-- Prove2me | Theorems.Thm_FirstPriceLearning_NonIID_theorem_8
-- name    : FirstPriceLearning.NonIID.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:12.843489+00:00
-- url     : https://prove2.me/theorems/9ac4761b-dcc1-4742-8b98-d6db2fe312b1
-- title:
--   Theorem 8, p. 34 — if the HOB law switches at an unknown value threshold, every bidding policy has expected regret $\Omega(T)$
-- statement:
--   Consider repeated first-price auctions over $T$ rounds in which the highest other bid $m_t$ has law $P$ when the private value satisfies $v_t<v^\star$ and law $Q$ when $v_t\ge v^\star$, independently across rounds, with full-information feedback ($m_t$ is revealed after round $t$). Only the threshold $v^\star$ is unknown to the bidder.
--
--   **Theorem 8.** There are an absolute constant $c>0$ and probability laws $P,Q$ on $[0,1]$ such that for every horizon $T$ and every (possibly randomized) bidding policy $\pi$, there exist a threshold $v^\star\in[0,1]$ and an oblivious value sequence $v_1,\dots,v_T\in[0,1]$ with
--   $$
--   \mathbb E\big[R_T(\pi;v^\star,v)\big]\ \ge\ c\,T,
--   $$
--   where
--   $$
--   R_T=\sum_{t=1}^T\Big(\max_{b\in[0,1]}\mathbb E_{m\sim L_t}\big[(v_t-b)\mathbb 1(b\ge m)\big]-(v_t-b_t)\mathbb 1(b_t\ge m_t)\Big),\qquad L_t=P\text{ if }v_t<v^\star,\ L_t=Q\text{ otherwise}.
--   $$
--
--   Learning with sublinear regret is thus impossible as soon as the HOB distribution depends on the private value, even through a single threshold and with $(P,Q)$ known: contrast the $\widetilde O(\sqrt T)$ bounds of the iid case.
--
--   **Formalization Note** $\Omega(T)$ is read as an absolute constant $c$ chosen before $T$ and $\pi$ (the proof gives $c=1/16$, which is not hard-coded). The laws $P,Q$ are also chosen before $T$ and $\pi$, so the policy may be tuned to them; this is how "the distributions $(P,Q)$ are revealed to the bidder" is encoded, and it is stronger than choosing $(P,Q)$ after $\pi$. Policies draw internal randomness once from a probability space, and the bid at round $t$ is a measurable function of that randomness, $v_1,\dots,v_t$ and $m_1,\dots,m_{t-1}$, with values in $[0,1]$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 34, Theorem 8 (model and regret on p. 33)

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Auction
import Definitions.Def_FirstPriceLearning_NonIID_ThresholdModel

namespace FirstPriceLearning.NonIID

open MeasureTheory

/-- Theorem 8, arXiv:2003.09795v7, p. 34: in the threshold model of p. 33 (`m_t ∼ P` if `v_t < v⋆`,
`m_t ∼ Q` if `v_t ≥ v⋆`, full-information feedback), every bidding policy has expected regret `Ω(T)`
for some threshold `v⋆` and some oblivious value sequence. The absolute constant `c` and the laws
`(P, Q)` are fixed before the horizon and the policy, so a policy may be tuned to `(P, Q)`. -/
theorem theorem_8 :
    ∃ c : ℝ, 0 < c ∧ ∃ P Q : Measure ℝ, IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
      P (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ Q (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ (T : ℕ) (π : FullInfoPolicy T), ∃ vstar : ℝ, vstar ∈ Set.Icc (0 : ℝ) 1 ∧
        ∃ v : Fin T → ℝ, (∀ t, v t ∈ Set.Icc (0 : ℝ) 1) ∧
          c * T ≤ expectedRegret π P Q vstar v := by sorry

end FirstPriceLearning.NonIID
