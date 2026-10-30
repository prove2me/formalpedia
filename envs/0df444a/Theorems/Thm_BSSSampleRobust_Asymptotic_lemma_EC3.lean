-- Prove2me | Theorems.Thm_BSSSampleRobust_Asymptotic_lemma_EC3
-- name    : BSSSampleRobust.Asymptotic.lemma_EC3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T22:27:40.042993+00:00
-- url     : https://prove2.me/theorems/93978de9-10c7-45df-aa80-241db70e7ad0
-- title:
--   Lemma EC.3 — Eventual empirical Wasserstein rate
-- statement:
--   Let $P$ be any Borel probability law on $\mathbb R^d$, $d\ge1$, with any fixed $\ell_p$ norm, $1\le p\le\infty$. Suppose Assumption 1 holds: $\mathbb E_P\exp(\|\xi\|^a)<\infty$ for some $a>1$. For iid samples with law $P$, let $\widehat P_N=N^{-1}\sum_{j=1}^N\delta_{\hat\xi^j}$ and let $W_1$ be the coupling infimum of expected transport distance. For every fixed $\bar\kappa>0$, set
--   $$\delta_N=\begin{cases}\bar\kappa N^{-1/2}\log N,&d=1,\\\bar\kappa N^{-1/d}(\log N)^2,&d\ge2.\end{cases}$$
--   Then $P^\infty$-almost surely, $W_1(P,\widehat P_N)\le\delta_N$ for all sufficiently large positive $N$. This includes dimension two and supplies the empirical transport rate used in the uniform estimate.
--
--   Differences from the source:
--   - encoding: finite-dimensional real spaces with any fixed lp norm, 1 ≤ p ≤ ∞ → PiLp over finite coordinates, Borel sigma algebras, and Fact (1 ≤ p); reason: coordinate relabeling preserves every allowed norm and every source instance; the ambient dimension is positive
--   - encoding: extended-real expectation and extrema with infinity minus infinity equal to positive infinity → EReal extrema and the referenced positive-part-first expectation, applied on the completed measure; reason: infeasibility gives positive infinity and unbounded extrema remain infinite; no integrability hypothesis is added
--   - encoding: samples indexed 1 through N, N positive, under the infinite iid product law → samples indexed by Fin N, drawn from the coordinates 0 through N-1 of Measure.infinitePi on natural numbers; reason: a shift of labels gives the same iid data; finite-sample assertions require N ≥ 1 and asymptotic assertions ignore N = 0
-- source:
--   Bertsimas, Shtern and Sturt (2023), A Data-Driven Approach to Multistage Stochastic Linear Optimization, Management Science, https://doi.org/10.1287/mnsc.2022.4352; published basis, supplied manuscript/e-companion artifact; Lemma EC.3, PDF page 61, printed page ec19

import Mathlib
import Definitions.Def_BSSSampleRobust_Asymptotic_Sampling

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BSSSampleRobust.Asymptotic

theorem lemma_EC3 (p : ℝ≥0∞) [Fact (1 ≤ p)] (d : ℕ) (hd : 0 < d)
    (P : Measure (Vec p (Fin d))) [IsProbabilityMeasure P]
    (h1 : lightTail P) (κ : ℝ) (hκ : 0 < κ) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => P), ∃ K : ℕ, ∀ N : ℕ, K ≤ N → 1 ≤ N →
      WassersteinDRO.Duality.wassersteinDistance 1 P
        (WassersteinDRO.Duality.empiricalDistribution (fun j : Fin N => ω j.val)) ≤
        ENNReal.ofReal (empiricalRate d κ N) := by sorry

end BSSSampleRobust.Asymptotic
