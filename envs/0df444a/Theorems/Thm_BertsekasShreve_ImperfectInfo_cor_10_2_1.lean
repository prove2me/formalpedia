-- Prove2me | Theorems.Thm_BertsekasShreve_ImperfectInfo_cor_10_2_1
-- name    : BertsekasShreve.ImperfectInfo.cor_10_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:41:34.352994+00:00
-- url     : https://prove2.me/theorems/4a0a5c5e-4b54-4f81-8bd0-5790ca6b301b
-- title:
--   Corollary 10.2.1 — $J^*_N(p)\le\int\hat J^*_N\,d\varphi(p)$
-- statement:
--   Let an (ISI) model with finite horizon $N$ and a statistic sufficient for control be given, and assume $(F^+,\hat F^+)$ or $(F^-,\hat F^-)$. Then for every $p\in P(S)$,
--   $$J^*_N(p)\le\int_{Y_0}\hat J^*_N(y_0)\,\varphi(p)(dy_0).$$
--
--   This is the easy half of the equality of optimal costs in Proposition 10.3.
--
--   **Formalization Note** Finite-horizon cases only; $\hat J^*_N$ is the infimum over all (PSI) policies $\hat\Pi'$, and the integral uses the book's convention $\infty-\infty=+\infty$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 254, Corollary 10.2.1 (Eq. (34) of Chapter 10)

import Mathlib
import Definitions.Def_BertsekasShreve_ImperfectInfo_SufficientStatistic

open MeasureTheory ProbabilityTheory

namespace BertsekasShreve.ImperfectInfo

/-- Corollary 10.2.1 (p. 254), finite horizon, under (F⁺, F̂⁺) or (F⁻, F̂⁻). -/
theorem cor_10_2_1 {S C Z : Type}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (M : ISIModel S C Z) {Y : ℕ → Type} [∀ k, TopologicalSpace (Y k)] [∀ k, MeasurableSpace (Y k)]
    (σ : SuffStat M Y)
    (hF : (M.Fplus ∧ σ.FhatPlus) ∨ (M.Fminus ∧ σ.FhatMinus))
    (p : ProbabilityMeasure S) :
    M.optCost p ≤ extIntegral (σ.phi p) σ.optCostHat := by sorry

end BertsekasShreve.ImperfectInfo
