-- Prove2me | Theorems.Thm_FairKMeans_lemma_28
-- name    : FairKMeans.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:30.920199+00:00
-- url     : https://prove2.me/theorems/31f398f5-7625-4a34-b763-553b13e9d422
-- title:
--   Lemma 28 — termination: at most $\lceil 576/\eta^2\rceil$ updates, ending $(\eta L_0)$-stationary
-- statement:
--   Let $\rho\ge1$, $\varepsilon\in(0,1]$, $\eta=\min\{1/10,\varepsilon/(3\rho)\}$, let the instance have a fair solution, and run Algorithm 1 with exact LP oracles (and any $k$-means oracle). Then the loop updates the relaxed solution at most $\lceil 576/\eta^2\rceil$ times, it ends by its stopping test $g\le\eta L_0/2$ (within its budget of $\lceil576/\eta^2\rceil+1$ iterations), and the relaxed solution $(T,\phi_T)$ at termination is a relaxed solution that is $(\eta L_0)$-stationary.
--
--   Together with Lemma 23 this gives the cost bound of Theorem 3.
--
--   Differences from the source:
--   - encoding: the loop repeat … until g ≤ ηL0/2 → at most ⌈576/η²⌉+1 iterations with a stop flag; the statement asserts the flag; reason: the budget is the paper's own iteration bound (p.36); the flag shows the test, not the budget, ended the loop
--   - encoding: LP solvers that return optimal solutions → oracles returning an optimal solution whenever one exists; reason: both LPs have optima in every call under the standing assumption
--   - encoding: standing assumption: the instance has a fair solution (p.19) → hypothesis HasFairSolution; reason: stated once for the whole analysis
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Lemma 28, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_WeightedKMeans
import Definitions.Def_FairKMeans_RelaxedSolution
import Definitions.Def_FairKMeans_CandidateSets
import Definitions.Def_FairKMeans_LPOracles
import Definitions.Def_FairKMeans_Algorithm1

namespace FairKMeans

/-- **Lemma 28 (Termination)**, p.34 (PDF 36). Cheng–Mo–Song–Ding, arXiv:2609.07974 (held
version, sha256 73e9312c…).

For an instance with a fair solution (p.19) and exact LP oracles, the loop of Algorithm 1
updates the relaxed solution at most `⌈576/η²⌉` times, it ends by its stopping test
`g ≤ ηL₀/2` (within the `⌈576/η²⌉ + 1` iterations of p.36), and the relaxed solution
`(T, φ_T)` at termination is `(ηL₀)`-stationary. -/
theorem lemma_28 (ρ ε : ℝ) (hρ : 1 ≤ ρ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) {d n m : ℕ}
    (I : Instance d n m) (hfair : HasFairSolution I) (fairLP : FairLPOracle d n)
    (lp29 : LP29Oracle d n) (KM : KMOracle d) (hF : IsFairLPOracle I fairLP)
    (hL : IsLP29Oracle I lp29) :
    (alg1 ρ ε I fairLP lp29 KM).updates ≤ ⌈576 / eta ρ ε ^ 2⌉₊ ∧
      (alg1 ρ ε I fairLP lp29 KM).stopped ∧
      IsRelaxed I (alg1 ρ ε I fairLP lp29 KM).relaxedφ ∧
      IsStationary I ρ (eta ρ ε * (alg1 ρ ε I fairLP lp29 KM).L₀)
        (alg1 ρ ε I fairLP lp29 KM).relaxedφ := by sorry

end FairKMeans
