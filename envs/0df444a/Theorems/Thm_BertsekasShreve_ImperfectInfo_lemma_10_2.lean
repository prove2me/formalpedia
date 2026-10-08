-- Prove2me | Theorems.Thm_BertsekasShreve_ImperfectInfo_lemma_10_2
-- name    : BertsekasShreve.ImperfectInfo.lemma_10_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:41:46.009143+00:00
-- url     : https://prove2.me/theorems/f241f54a-3699-42cf-8616-3b06295286d4
-- title:
--   Lemma 10.2 — every (ISI) policy is matched in cost by a Markov (PSI) policy
-- statement:
--   Let an (ISI) model with finite horizon $N$ and a statistic sufficient for control be given, and assume $(F^+,\hat F^+)$ or $(F^-,\hat F^-)$. Given $p\in P(S)$ and a policy $\pi\in\Pi$ for (ISI), there exists a Markov (PSI) policy $\hat\pi\in\hat\Pi$ such that
--   $$J_{N,\pi}(p)=\int_{Y_0}\hat J_{N,\hat\pi}(y_0)\,\varphi(p)(dy_0).$$
--
--   Together with Corollary 10.2.1 this yields the equality of optimal costs in Proposition 10.3.
--
--   **Formalization Note** Finite-horizon cases only. The existential ranges over Markov (PSI) policies $\hat\mu_k(du\mid y_k)$ satisfying the constraints $\hat\mu_k(\hat U_k(y_k)\mid y_k)=1$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 255, Lemma 10.2 (Eq. (36) of Chapter 10)

import Mathlib
import Definitions.Def_BertsekasShreve_ImperfectInfo_SufficientStatistic

open MeasureTheory ProbabilityTheory

namespace BertsekasShreve.ImperfectInfo

/-- Lemma 10.2 (p. 255), finite horizon, under (F⁺, F̂⁺) or (F⁻, F̂⁻). -/
theorem lemma_10_2 {S C Z : Type}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (M : ISIModel S C Z) {Y : ℕ → Type} [∀ k, TopologicalSpace (Y k)] [∀ k, MeasurableSpace (Y k)]
    (σ : SuffStat M Y)
    (hF : (M.Fplus ∧ σ.FhatPlus) ∨ (M.Fminus ∧ σ.FhatMinus))
    (p : ProbabilityMeasure S)
    (π : (k : ℕ) → ProbabilityMeasure S × Info Z C k → ProbabilityMeasure C)
    (hπ : M.IsPolicy π) :
    ∃ μ : (k : ℕ) → Y k → ProbabilityMeasure C, σ.IsMarkovPolicy μ ∧
      M.cost π p = extIntegral (σ.phi p) (σ.costHat (markovToPolicy μ)) := by sorry

end BertsekasShreve.ImperfectInfo
