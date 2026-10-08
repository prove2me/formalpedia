-- Prove2me | Theorems.Thm_BertsekasShreve_ImperfectInfo_prop_10_2
-- name    : BertsekasShreve.ImperfectInfo.prop_10_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:41:40.698102+00:00
-- url     : https://prove2.me/theorems/b41ee8ad-e91e-4690-a2d1-da031d6be45b
-- title:
--   Proposition 10.2 — a Markov (PSI) policy has the same cost in (ISI) and, averaged over $\varphi(p)$, in (PSI)
-- statement:
--   Let an (ISI) model with finite horizon $N$ and a statistic sufficient for control be given, and assume $(F^+,\hat F^+)$ or $(F^-,\hat F^-)$, i.e. $(F^+)$ for (ISI) together with $(\hat F^+)$ for (PSI), or $(F^-)$ together with $(\hat F^-)$. Then for every $p\in P(S)$ and every Markov (PSI) policy $\hat\pi\in\hat\Pi$, regarded as a policy for (ISI),
--   $$J_{N,\hat\pi}(p)=\int_{Y_0}\hat J_{N,\hat\pi}(y_0)\,\varphi(p)(dy_0).$$
--
--   The cost of a policy that uses only the statistic can thus be computed entirely in the perfect state information model.
--
--   **Formalization Note** Only the finite-horizon cases $(F^+,\hat F^+)$ and $(F^-,\hat F^-)$ of the book's statement are formalized; the infinite-horizon cases $(P,\hat P)$, $(N,\hat N)$, $(D,\hat D)$ are out of scope. Integrals use the book's convention $\infty-\infty=+\infty$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 254, Proposition 10.2 (Eq. (33) of Chapter 10)

import Mathlib
import Definitions.Def_BertsekasShreve_ImperfectInfo_SufficientStatistic

open MeasureTheory ProbabilityTheory

namespace BertsekasShreve.ImperfectInfo

/-- Proposition 10.2 (p. 254), finite horizon, under (F⁺, F̂⁺) or (F⁻, F̂⁻). -/
theorem prop_10_2 {S C Z : Type}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (M : ISIModel S C Z) {Y : ℕ → Type} [∀ k, TopologicalSpace (Y k)] [∀ k, MeasurableSpace (Y k)]
    (σ : SuffStat M Y)
    (hF : (M.Fplus ∧ σ.FhatPlus) ∨ (M.Fminus ∧ σ.FhatMinus))
    (p : ProbabilityMeasure S) (μ : (k : ℕ) → Y k → ProbabilityMeasure C)
    (hμ : σ.IsMarkovPolicy μ) :
    M.cost (σ.toISI μ) p = extIntegral (σ.phi p) (σ.costHat (markovToPolicy μ)) := by sorry

end BertsekasShreve.ImperfectInfo
