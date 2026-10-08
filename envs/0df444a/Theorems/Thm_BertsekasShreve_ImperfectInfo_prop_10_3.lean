-- Prove2me | Theorems.Thm_BertsekasShreve_ImperfectInfo_prop_10_3
-- name    : BertsekasShreve.ImperfectInfo.prop_10_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:42:19.868504+00:00
-- url     : https://prove2.me/theorems/79a497e0-9af5-4262-8b42-cb6bdfc00c82
-- title:
--   Proposition 10.3 — $J^*_N(p)=\int_{Y_0}\hat J^*_N\,d\varphi(p)$, and (nearly) optimal (PSI) policies are (nearly) optimal for (ISI)
-- statement:
--   Let an (ISI) model with finite horizon $N$, a statistic $(\eta_0,\dots,\eta_{N-1})$ sufficient for control, and the associated (PSI) model be given, and assume $(F^+,\hat F^+)$ or $(F^-,\hat F^-)$. Then:
--
--   1. for every $p\in P(S)$,
--   $$J^*_N(p)=\int_{Y_0}\hat J^*_N(y_0)\,\varphi(p)(dy_0);$$
--   2. if a Markov (PSI) policy $\hat\pi$ is optimal for (PSI), then $\hat\pi$, regarded as a policy for (ISI), is optimal;
--   3. if $\hat\pi$ is $\varphi(p)$-optimal, then it is optimal at $p$ for (ISI);
--   4. if $\varepsilon>0$ and $\hat\pi$ is weakly $\varphi(p)$-$\varepsilon$-optimal, then it is $\varepsilon$-optimal at $p$ for (ISI);
--   5. under $(F^+,\hat F^+)$: if $\varepsilon>0$ and $\hat\pi$ is $\varepsilon$-optimal for (PSI), then it is $\varepsilon$-optimal for (ISI).
--
--   Here a Markov (PSI) policy $\hat\mu_k(du\mid y_k)$ acts in (ISI) by $\mu_k(du\mid p;i_k)=\hat\mu_k(du\mid\eta_k(p;i_k))$, and the notions of optimality are those of Definitions 8.3, 10.5 and 10.8.
--
--   This is the main reduction theorem of Chapter 10: an imperfect state information problem is solved by solving the perfect state information problem whose state is the sufficient statistic, and its optimal cost is the $\varphi(p)$-average of the (PSI) optimal cost.
--
--   **Formalization Note** Only the finite-horizon cases $(F^+,\hat F^+)$, $(F^-,\hat F^-)$ of the book's statement are formalized; the infinite-horizon cases $(P,\hat P)$, $(N,\hat N)$, $(D,\hat D)$ are out of scope. The policies $\hat\pi$ in items 2–5 are Markov (PSI) policies, the class for which the book's proof (via Proposition 10.2 and Lemma 10.1) and the sentence preceding the proposition place them. Integrals use the book's convention $\infty-\infty=+\infty$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 256, Proposition 10.3 (Eq. (41) of Chapter 10); Definition 10.8, p. 256

import Mathlib
import Definitions.Def_BertsekasShreve_ImperfectInfo_SufficientStatistic

open MeasureTheory ProbabilityTheory

namespace BertsekasShreve.ImperfectInfo

/-- Proposition 10.3 (p. 256), finite horizon, under (F⁺, F̂⁺) or (F⁻, F̂⁻). -/
theorem prop_10_3 {S C Z : Type}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (M : ISIModel S C Z) {Y : ℕ → Type} [∀ k, TopologicalSpace (Y k)] [∀ k, MeasurableSpace (Y k)]
    (σ : SuffStat M Y)
    (hF : (M.Fplus ∧ σ.FhatPlus) ∨ (M.Fminus ∧ σ.FhatMinus)) :
    (∀ p : ProbabilityMeasure S, M.optCost p = extIntegral (σ.phi p) σ.optCostHat) ∧
    (∀ μ : (k : ℕ) → Y k → ProbabilityMeasure C, σ.IsMarkovPolicy μ →
      σ.IsOptimalHat (markovToPolicy μ) → M.IsOptimal (σ.toISI μ)) ∧
    (∀ μ : (k : ℕ) → Y k → ProbabilityMeasure C, σ.IsMarkovPolicy μ →
      ∀ p : ProbabilityMeasure S,
        σ.IsQOptimal (σ.phi p) (markovToPolicy μ) → M.IsOptimalAt (σ.toISI μ) p) ∧
    (∀ μ : (k : ℕ) → Y k → ProbabilityMeasure C, σ.IsMarkovPolicy μ →
      ∀ (p : ProbabilityMeasure S) (ε : ℝ), 0 < ε →
        σ.IsWeaklyEpsOptimal (σ.phi p) ε (markovToPolicy μ) →
          M.IsEpsOptimalAt (σ.toISI μ) p ε) ∧
    (M.Fplus ∧ σ.FhatPlus →
      ∀ μ : (k : ℕ) → Y k → ProbabilityMeasure C, σ.IsMarkovPolicy μ →
        ∀ ε : ℝ, 0 < ε → σ.IsEpsOptimalHat ε (markovToPolicy μ) →
          M.IsEpsOptimal (σ.toISI μ) ε) := by sorry

end BertsekasShreve.ImperfectInfo
