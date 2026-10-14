-- Prove2me | Theorems.Thm_FirstPriceLearning_NonIID_oracle_bid
-- name    : FirstPriceLearning.NonIID.oracle_bid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:10.972876+00:00
-- url     : https://prove2.me/theorems/69d076ff-71cd-460f-8a0e-2e4a79f79076
-- title:
--   Proof of Theorem 8, p. 34 — $v_t\in[1/4,3/4]$ and the oracle bids $b^\star_t=m_t=\frac18\mathbb 1(v_t\ge v^\star)$
-- statement:
--   Take $P=\delta_0$ and $Q=\delta_{1/8}$ (so $m_t\equiv0$ under $P$ and $m_t\equiv1/8$ under $Q$), a sign vector $u\in\{\pm1\}^T$, the threshold $v^\star=f(u)$ and the values $v_1=\frac12$, $v_{t+1}=v_t+u_t/2^{t+2}$. For every round $t$:
--
--   1. $v_t\in[\tfrac14,\tfrac34]$;
--   2. the oracle reward under the law $L_t$ of $m_t$ ($P$ if $v_t<v^\star$, $Q$ otherwise) is
--   $$
--   \max_{b\in[0,1]}\mathbb E_{m\sim L_t}\big[(v_t-b)\mathbb 1(b\ge m)\big]=v_t-m_t,\qquad m_t=\tfrac18\,\mathbb 1(v_t\ge v^\star);
--   $$
--   3. the bid $b^\star_t=m_t$ attains this maximum.
--
--   Summed over rounds this is the oracle's revenue $\sum_t(v_t-m_t)$ on p. 34.
--
--   **Formalization Note** The maximum is the supremum over $b\in[0,1]$ of $R(v_t,b)=(v_t-b)G_{L_t}(b)$, with $G_{L_t}$ the CDF of $L_t$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 34, proof of Theorem 8 (choice of P, Q and the oracle performance)

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Auction
import Definitions.Def_FirstPriceLearning_NonIID_ThresholdModel
import Definitions.Def_FirstPriceLearning_NonIID_HardInstance

namespace FirstPriceLearning.NonIID

open MeasureTheory

/-- Proof of Theorem 8, arXiv:2003.09795v7, p. 34 (oracle performance): with `P = δ_0`,
`Q = δ_{1/8}`, `u ∈ {±1}^T`, `v⋆ = f(u)` and the values `v_t` of p. 34, every `v_t` lies in
`[1/4, 3/4]`, the oracle's reward at round `t` is `v_t − m_t` with `m_t = (1/8)·𝟙(v_t ≥ v⋆)`, and the
bid `b⋆_t = m_t` attains it. -/
theorem oracle_bid (T : ℕ) (u : Fin T → ℝ) (hu : ∀ s, u s = 1 ∨ u s = -1) (t : Fin T) :
    valueSeq u t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) ∧
      FirstPriceLearning.Stochastic.oracle (hobLaw (Measure.dirac 0) (Measure.dirac (1 / 8)) (fval u) (valueSeq u t))
          (valueSeq u t) =
        valueSeq u t - 1 / 8 * (if fval u ≤ valueSeq u t then 1 else 0) ∧
      FirstPriceLearning.Stochastic.expReward (hobLaw (Measure.dirac 0) (Measure.dirac (1 / 8)) (fval u) (valueSeq u t))
          (valueSeq u t) (1 / 8 * (if fval u ≤ valueSeq u t then 1 else 0)) =
        FirstPriceLearning.Stochastic.oracle (hobLaw (Measure.dirac 0) (Measure.dirac (1 / 8)) (fval u) (valueSeq u t))
          (valueSeq u t) := by sorry

end FirstPriceLearning.NonIID
