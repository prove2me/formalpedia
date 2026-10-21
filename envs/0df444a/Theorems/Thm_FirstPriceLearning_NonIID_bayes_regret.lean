-- Prove2me | Theorems.Thm_FirstPriceLearning_NonIID_bayes_regret
-- name    : FirstPriceLearning.NonIID.bayes_regret
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:10.486001+00:00
-- url     : https://prove2.me/theorems/20bfd443-fb9d-4c38-a5f0-9e3d27a2b888
-- title:
--   Proof of Theorem 8, p. 34 — under the prior $\nu$ the average regret of every policy is at least $T/16$
-- statement:
--   Take $P=\delta_0$, $Q=\delta_{1/8}$ and the prior $\nu$ of p. 34: a sign vector $u\in\{\pm1\}^T$ is uniform, $v^\star=f(u)=\frac12+\frac14\sum_t u_t/2^t$, and the values are $v_1=\frac12$, $v_{t+1}=v_t+u_t/2^{t+2}$. Then for every horizon $T$ and every randomized full-information bidding policy $\pi$,
--   $$
--   \frac{1}{2^T}\sum_{u\in\{\pm1\}^T}\mathbb E\big[R_T(\pi;\,v^\star=f(u),\,v(u))\big]\ \ge\ \frac{T}{16},
--   $$
--   where $\mathbb E[R_T(\pi;v^\star,v)]$ is the expected regret in the threshold model with HOB law $P$ below $v^\star$ and $Q$ at or above it.
--
--   This is the Bayesian lower bound from which Theorem 8 follows: some sign vector does at least as badly as the average.
--
--   **Formalization Note** The sum runs over Boolean vectors $\sigma\in\{\mathrm{true},\mathrm{false}\}^T$ with $u_t=+1$ for true and $-1$ for false. The paper's display also states $\mathbb E_\nu[\sum_t(1/8-m_t)]=T/16$ as an identity; only the resulting lower bound on the average regret is formalized.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 34, proof of Theorem 8, last display

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Auction
import Definitions.Def_FirstPriceLearning_NonIID_ThresholdModel
import Definitions.Def_FirstPriceLearning_NonIID_HardInstance

namespace FirstPriceLearning.NonIID

open MeasureTheory

/-- Proof of Theorem 8, arXiv:2003.09795v7, p. 34 (last display): with `P = δ_0`, `Q = δ_{1/8}`, and
`(v⋆, v)` drawn from the prior `ν` (uniform signs `u ∈ {±1}^T`, `v⋆ = f(u)`, the values `v_t` of
p. 34), the average regret of every full-information policy is at least `T/16`. -/
theorem bayes_regret (T : ℕ) (π : FullInfoPolicy T) :
    (T : ℝ) / 16 ≤
      (1 / 2 ^ T : ℝ) * ∑ σ : Fin T → Bool,
        expectedRegret π (Measure.dirac 0) (Measure.dirac (1 / 8))
          (fval (fun t => pm (σ t))) (valueSeq (fun t => pm (σ t))) := by sorry

end FirstPriceLearning.NonIID
